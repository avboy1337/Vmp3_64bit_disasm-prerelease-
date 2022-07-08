use inkwell::{
    attributes::{Attribute, AttributeLoc},
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    memory_buffer::MemoryBuffer,
    module::Module,
    passes::PassManager,
    values::{
        BasicValue, BasicValueEnum, CallableValue, FunctionValue, InstructionValue, PointerValue,
    },
};
use petgraph::{algo::dominators, graphmap::GraphMap, EdgeDirection::Incoming};
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    error::Error,
    path::Path,
};

use crate::{
    symbolic::get_possible_solutions,
    vm_handler::{Registers, VmContext},
    vm_matchers::HandlerVmInstruction,
};
pub struct VmLifter<'ctx> {
    context: &'ctx Context,
    module:  RefCell<Module<'ctx>>,
    builder: Builder<'ctx>,
}
// This leaks memory :(
impl<'ctx> VmLifter<'ctx> {
    pub fn lift_helper_stub(&self,
                            vm_context: &VmContext,
                            handlers: &[(u64, HandlerVmInstruction, u64)]) {
        let helper_stub = self.create_helper_stub(vm_context.initial_vip);
        self.lift_into_helper_stub(vm_context, handlers, &helper_stub);
    }

    pub fn slice_vip(&self,
                     control_flow_graph: &GraphMap<u64, (), petgraph::Directed>,
                     mut input_vip: u64,
                     root_vip: u64,
                     max_pred_block_count: Option<u64>)
                     -> Result<Vec<u64>, Box<dyn Error>> {
        self.output_module();

        let mut slice_blocks = vec![input_vip];

        println!("Computing dominators");
        let dominator_info = dominators::simple_fast(control_flow_graph, root_vip);
        println!("Done computing dominators");

        let mut loopcount = 0;
        'outer: loop {
            let pred_nodes = control_flow_graph.edges_directed(input_vip, Incoming)
                                               .map(|edge| edge.0)
                                               .collect::<HashSet<u64>>();

            if pred_nodes.is_empty() || pred_nodes.len() > 1 {
                break 'outer;
            }

            let mut temp_slice_blocks = Vec::new();
            for dominator in dominator_info.dominators(input_vip).unwrap() {
                if pred_nodes.contains(&dominator) {
                    temp_slice_blocks.push(dominator);
                    input_vip = dominator;
                    break;
                }
            }

            loopcount += 1;
            println!("Loop iteration -> {}", loopcount);
            slice_blocks.extend_from_slice(&temp_slice_blocks);

            if let Some(max_count) = max_pred_block_count {
                if loopcount == max_count {
                    break 'outer;
                }
            }
        }

        self.create_helper_slicevpc(&slice_blocks);
        self.optimize_module();
        self.output_bitcode();

        let possible_solutions_vip = get_possible_solutions("helperslicevpc")?;

        self.reload_module()?;

        Ok(possible_solutions_vip)
    }

    #[allow(dead_code)]
    pub fn print_module(&self) {
        self.module.borrow().print_to_stderr();
    }

    #[allow(dead_code)]
    pub fn verify_module(&self) {
        self.module.borrow().verify().unwrap();
    }

    pub fn output_module(&self) {
        self.module.borrow().print_to_file("devirt.ll").unwrap();
    }

    pub fn reload_module(&self) -> Result<(), Box<dyn Error>> {
        let path = Path::new("devirt.ll");
        let memory_buffer = MemoryBuffer::create_from_file(path)?;
        let new_module = self.context.create_module_from_ir(memory_buffer)?;

        *self.module.borrow_mut() = new_module;

        Ok(())
    }

    pub fn output_bitcode(&self) {
        self.module
            .borrow()
            .write_bitcode_to_path(std::path::Path::new("devirt.bc"));
    }

    #[allow(dead_code)]
    pub fn print_function(&self,
                          func_name: &str) {
        let function = self.module.borrow().get_function(func_name);

        match function {
            Some(func_val) => func_val.print_to_stderr(),
            None => {
                println!("Function not found {}", func_name)
            },
        }
    }

    pub fn new() -> Self {
        let context = Box::leak(Box::new(inkwell::context::Context::create()));

        let vmprotect_helpers = include_bytes!("VMProtectHelpers_64.ll");

        let memory_buffer =
            MemoryBuffer::create_from_memory_range_copy(vmprotect_helpers.as_slice(),
                                                        "vmp_helpers");
        let module = context.create_module_from_ir(memory_buffer).unwrap();
        let builder = context.create_builder();

        let undef = module.get_global("__undef").unwrap();
        undef.set_initializer(&context.i64_type().get_undef());

        Self { context,
               module: RefCell::new(module),
               builder }
    }

    pub fn optimize_module_no_global_delete(&self) {
        let module_passmanager: PassManager<Module<'_>> = PassManager::create(());

        module_passmanager.add_always_inliner_pass();
        module_passmanager.add_basic_alias_analysis_pass();
        module_passmanager.add_type_based_alias_analysis_pass();
        module_passmanager.add_scoped_no_alias_aa_pass();
        module_passmanager.add_cfg_simplification_pass();
        module_passmanager.add_scalar_repl_aggregates_pass();
        module_passmanager.add_early_cse_mem_ssa_pass();
        module_passmanager.add_instruction_simplify_pass();
        module_passmanager.add_instruction_combining_pass();
        module_passmanager.add_cfg_simplification_pass();
        module_passmanager.add_gvn_pass();
        module_passmanager.add_dead_store_elimination_pass();
        module_passmanager.add_instruction_simplify_pass();
        module_passmanager.add_instruction_combining_pass();
        module_passmanager.add_cfg_simplification_pass();
        module_passmanager.add_strip_symbol_pass();

        for _ in 0 .. 3 {
            module_passmanager.run_on(&self.module.borrow());
        }

        let i64_type = self.context.i64_type();
        let undef = self.module.borrow().get_global("__undef").unwrap();
        undef.set_initializer(&i64_type.get_undef());
        undef.set_constant(true);

        for _ in 0 .. 3 {
            module_passmanager.run_on(&self.module.borrow());
        }
    }

    pub fn optimize_module(&self) {
        let module_passmanager: PassManager<Module<'_>> = PassManager::create(());

        module_passmanager.add_always_inliner_pass();
        module_passmanager.add_basic_alias_analysis_pass();
        module_passmanager.add_type_based_alias_analysis_pass();
        module_passmanager.add_scoped_no_alias_aa_pass();
        module_passmanager.add_cfg_simplification_pass();
        module_passmanager.add_scalar_repl_aggregates_pass();
        module_passmanager.add_early_cse_mem_ssa_pass();
        module_passmanager.add_instruction_simplify_pass();
        module_passmanager.add_instruction_combining_pass();
        module_passmanager.add_cfg_simplification_pass();
        module_passmanager.add_gvn_pass();
        module_passmanager.add_dead_store_elimination_pass();
        module_passmanager.add_instruction_simplify_pass();
        module_passmanager.add_instruction_combining_pass();
        module_passmanager.add_cfg_simplification_pass();
        module_passmanager.add_strip_symbol_pass();

        for _ in 0 .. 3 {
            module_passmanager.run_on(&self.module.borrow());
        }

        let i64_type = self.context.i64_type();
        let undef = self.module.borrow().get_global("__undef").unwrap();
        undef.set_initializer(&i64_type.get_undef());
        undef.set_constant(true);

        for _ in 0 .. 3 {
            module_passmanager.run_on(&self.module.borrow());
        }

        let i8_type = self.context.i8_type();
        let ram = self.module.borrow().get_global("RAM").unwrap();
        ram.set_initializer(&i8_type.array_type(0).const_array(&[]));
        ram.set_constant(true);
    }

    #[allow(dead_code)]
    pub fn fix_arg_names(&self,
                         helper_function_name: &str) {
        let helper_function = self.module
                                  .borrow()
                                  .get_function(helper_function_name)
                                  .unwrap();
        let param_names = ["rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp", "r8", "r9",
                           "r10", "r11", "r12", "r13", "r14", "r15", "flags", "KEY_STUB",
                           "RET_ADDR", "REL_ADDR"];

        for (i, (&name, param)) in
            std::iter::zip(param_names.iter(), helper_function.get_param_iter()).enumerate()
        {
            param.set_name(name);

            if name != "KEY_STUB" && name != "RET_ADDR" && name != "REL_ADDR" {
                helper_function.add_attribute(AttributeLoc::Param(i as _), self.context.create_enum_attribute(Attribute::get_named_enum_kind_id("noalias"), 0));
            }
        }
    }
    fn create_helper_stub(&self,
                          start_vip: u64)
                          -> FunctionValue {
        let helper_stub_def = self.module
                                  .borrow()
                                  .get_function("HelperStub")
                                  .expect("Could not find HelperStub in llvm ir file");
        let helper_stub_type = helper_stub_def.get_type();

        let helper_stub = self.module
                              .borrow()
                              .add_function(&format!("helperstub_{:x}", start_vip),
                                            helper_stub_type,
                                            None);
        let entry_bb = self.context.append_basic_block(helper_stub, "");

        let param_names = ["rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp", "r8", "r9",
                           "r10", "r11", "r12", "r13", "r14", "r15", "flags", "KEY_STUB",
                           "RET_ADDR", "REL_ADDR", "vsp", "vip", "vmregs", "slots"];
        for (i, (&name, param)) in
            std::iter::zip(param_names.iter(), helper_stub.get_param_iter()).enumerate()
        {
            param.set_name(name);

            if name != "KEY_STUB" && name != "RET_ADDR" && name != "REL_ADDR" {
                helper_stub.add_attribute(AttributeLoc::Param(i as _), self.context.create_enum_attribute(Attribute::get_named_enum_kind_id("noalias"), 0));
            }
        }

        self.builder.position_at_end(entry_bb);

        let vip_ptr = get_param_vip(&helper_stub);
        let vip = self.builder.build_load(vip_ptr, "");
        self.builder.build_return(Some(&vip));

        helper_stub.add_attribute(
            inkwell::attributes::AttributeLoc::Function,
            self.context
                .create_enum_attribute(Attribute::get_named_enum_kind_id("alwaysinline"), 0),
        );

        helper_stub
    }

    pub fn lift_vm_instruction(&self,
                               vm_context: &VmContext,
                               vm_instruction: &HandlerVmInstruction,
                               helper_stub: &FunctionValue) {
        // println!("Lifting -> {}", vm_instruction);
        match vm_instruction {
            HandlerVmInstruction::Pop(size, reg_offset) => {
                self.lift_pop(*size, *reg_offset, helper_stub);
            },
            HandlerVmInstruction::Push(size, reg_offset) => {
                self.lift_push(*size, *reg_offset, helper_stub);
            },
            HandlerVmInstruction::PushImm64(imm) => {
                self.lift_push_imm64(*imm, helper_stub);
            },
            HandlerVmInstruction::PushImm32(imm) => {
                self.lift_push_imm32(*imm, helper_stub);
            },
            HandlerVmInstruction::PushImm16(imm) => {
                self.lift_push_imm16(*imm, helper_stub);
            },
            HandlerVmInstruction::PushImm8(imm) => {
                self.lift_push_imm16(*imm as u16, helper_stub);
            },
            HandlerVmInstruction::PushVsp(size) => {
                self.lift_generic_handler(*size, "PUSH_VSP", helper_stub);
            },
            HandlerVmInstruction::PopVsp(size) => {
                self.lift_generic_handler(*size, "POP_VSP", helper_stub);
            },
            HandlerVmInstruction::Add(size) => {
                self.lift_generic_handler(*size, "ADD", helper_stub);
            },
            HandlerVmInstruction::Mul(size) => {
                self.lift_generic_handler(*size, "MUL", helper_stub);
            },
            HandlerVmInstruction::Imul(size) => {
                self.lift_generic_handler(*size, "IMUL", helper_stub);
            },
            HandlerVmInstruction::Shr(size) => {
                self.lift_generic_handler(*size, "SHR", helper_stub);
            },
            HandlerVmInstruction::Shl(size) => {
                self.lift_generic_handler(*size, "SHL", helper_stub);
            },
            HandlerVmInstruction::Shrd(size) => {
                self.lift_generic_handler(*size, "SHRD", helper_stub);
            },
            HandlerVmInstruction::Shld(size) => {
                self.lift_generic_handler(*size, "SHLD", helper_stub);
            },
            HandlerVmInstruction::Nand(size) => {
                self.lift_generic_handler(*size, "NAND", helper_stub);
            },
            HandlerVmInstruction::Nor(size) => {
                self.lift_generic_handler(*size, "NOR", helper_stub);
            },
            HandlerVmInstruction::Fetch(size) => {
                self.lift_generic_handler(*size, "LOAD_DS", helper_stub);
            },
            HandlerVmInstruction::Store(size) => {
                self.lift_generic_handler(*size, "STORE_DS", helper_stub);
            },
            HandlerVmInstruction::VmExit => {
                self.lift_vm_exit(vm_context, helper_stub);
            },
            HandlerVmInstruction::JumpDec => {
                self.lift_jump_sem(helper_stub, "JUMP_DEC");
            },
            HandlerVmInstruction::JumpInc => {
                self.lift_jump_sem(helper_stub, "JUMP_INC");
            },
            HandlerVmInstruction::JumpDecVspChange => {
                self.lift_jump_sem(helper_stub, "JUMP_DEC");
            },
            HandlerVmInstruction::JumpIncVspChange => {
                self.lift_jump_sem(helper_stub, "JUMP_INC");
            },
            HandlerVmInstruction::JumpDecVspXchng => {
                self.lift_jump_sem(helper_stub, "JUMP_DEC");
            },
            HandlerVmInstruction::JumpIncVspXchng => {
                self.lift_jump_sem(helper_stub, "JUMP_INC");
            },
            HandlerVmInstruction::Nop => {
                // Yep nothing
            },
            HandlerVmInstruction::UnknownByteOperand => todo!("Unkwnown handler"),
            HandlerVmInstruction::UnknownWordOperand => todo!("Unkwnown handler"),
            HandlerVmInstruction::UnknownDwordOperand => todo!("Unkwnown handler"),
            HandlerVmInstruction::UnknownQwordOperand => todo!("Unkwnown handler"),
            HandlerVmInstruction::UnknownNoOperand => todo!("Unkwnown handler"),
            HandlerVmInstruction::UnknownNoVipChange => todo!("Unkwnown handler"),
            HandlerVmInstruction::Unknown => todo!("Unkwnown handler"),
        }
    }

    fn lift_jump_sem(&self,
                     stub_function: &FunctionValue,
                     semantic_name: &str) {
        let vsp = get_param_vsp(stub_function);
        let vip = get_param_vip(stub_function);

        let a_semantic = self.get_semantic(&format!("SEM_{}", semantic_name));
        self.builder
            .build_call(a_semantic, &[vsp.into(), vip.into()], "");
    }

    fn lift_generic_handler(&self,
                            size: usize,
                            sem_base_name: &str,
                            helper_stub: &FunctionValue) {
        let vsp = get_param_vsp(helper_stub);

        let semantic = self.get_semantic(&format!("SEM_{}_{}", sem_base_name, size * 8));

        self.builder.build_call(semantic, &[vsp.into()], "");
    }
    fn lift_push_imm64(&self,
                       imm64: u64,
                       helper_stub: &FunctionValue) {
        let vsp = get_param_vsp(helper_stub);
        let i64_type = self.context.i64_type();

        let sem_push_imm64 = self.get_semantic("SEM_PUSH_IMM_64");
        let imm64_llvm = i64_type.const_int(imm64, false);

        self.builder
            .build_call(sem_push_imm64, &[vsp.into(), imm64_llvm.into()], "");
    }

    fn lift_push_imm32(&self,
                       imm32: u32,
                       helper_stub: &FunctionValue) {
        let vsp = get_param_vsp(helper_stub);
        let i32_type = self.context.i32_type();

        let sem_push_imm32 = self.get_semantic("SEM_PUSH_IMM_32");
        let imm32_llvm = i32_type.const_int(imm32 as u64, false);

        self.builder
            .build_call(sem_push_imm32, &[vsp.into(), imm32_llvm.into()], "");
    }

    fn lift_push_imm16(&self,
                       imm16: u16,
                       helper_stub: &FunctionValue) {
        let vsp = get_param_vsp(helper_stub);
        let i16_type = self.context.i16_type();

        let sem_push_imm16 = self.get_semantic("SEM_PUSH_IMM_16");
        let imm16_llvm = i16_type.const_int(imm16 as u64, false);

        self.builder
            .build_call(sem_push_imm16, &[vsp.into(), imm16_llvm.into()], "");
    }

    fn lift_push(&self,
                 size: usize,
                 reg_offset: u8,
                 helper_stub: &FunctionValue) {
        let vsp = get_param_vsp(helper_stub);
        let vm_regs = get_param_vm_regs(helper_stub);
        let i64_type = self.context.i64_type();

        let register_number = reg_offset / 8;
        let intra_register_offset = reg_offset % 8;

        let select_vm_reg = unsafe {
            self.builder.build_gep(vm_regs,
                                   &[i64_type.const_int(register_number as _, false)],
                                   "vm_reg")
        };

        let select_vm_reg =
            self.builder.build_pointer_cast(select_vm_reg,
                                            i64_type.ptr_type(inkwell::AddressSpace::Generic),
                                            "");

        let vm_reg = self.builder.build_load(select_vm_reg, "");

        match size {
            8 => {
                let sem_push_vmreg64 = self.get_semantic("SEM_PUSH_VMREG_64");

                self.builder
                    .build_call(sem_push_vmreg64, &[vsp.into(), vm_reg.into()], "");
            },
            4 => match intra_register_offset {
                0 => {
                    let sem_push_vmreg32_low = self.get_semantic("SEM_PUSH_VMREG_32_LOW");

                    self.builder
                        .build_call(sem_push_vmreg32_low, &[vsp.into(), vm_reg.into()], "");
                },
                4 => {
                    let sem_push_vmreg32_high = self.get_semantic("SEM_PUSH_VMREG_32_HIGH");

                    self.builder
                        .build_call(sem_push_vmreg32_high, &[vsp.into(), vm_reg.into()], "");
                },
                _ => unreachable!(),
            },
            2 => match intra_register_offset {
                0 => {
                    let sem_push_vmreg16_lowlow = self.get_semantic("SEM_PUSH_VMREG_16_LOWLOW");

                    self.builder
                        .build_call(sem_push_vmreg16_lowlow, &[vsp.into(), vm_reg.into()], "");
                },
                2 => {
                    let sem_push_vmreg16_lowhigh = self.get_semantic("SEM_PUSH_VMREG_16_LOWHIGH");

                    self.builder
                        .build_call(sem_push_vmreg16_lowhigh, &[vsp.into(), vm_reg.into()], "");
                },
                4 => {
                    let sem_push_vmreg16_highlow = self.get_semantic("SEM_PUSH_VMREG_16_HIGHLOW");

                    self.builder
                        .build_call(sem_push_vmreg16_highlow, &[vsp.into(), vm_reg.into()], "");
                },
                6 => {
                    let sem_push_vmreg16_highhigh = self.get_semantic("SEM_PUSH_VMREG_16_HIGHHIGH");

                    self.builder
                        .build_call(sem_push_vmreg16_highhigh, &[vsp.into(), vm_reg.into()], "");
                },
                _ => unreachable!(),
            },

            1 => {
                assert!(intra_register_offset == 1 || intra_register_offset == 0);
                match intra_register_offset {
                    0 => {
                        let sem_push_vmreg8_low = self.get_semantic("SEM_PUSH_VMREG_8_LOW");

                        self.builder.build_call(sem_push_vmreg8_low,
                                                &[vsp.into(), select_vm_reg.into()],
                                                "");
                    },
                    1 => {
                        let sem_push_vmreg8_high = self.get_semantic("SEM_PUSH_VMREG_8_HIGH");

                        self.builder.build_call(sem_push_vmreg8_high,
                                                &[vsp.into(), select_vm_reg.into()],
                                                "");
                    },
                    _ => unreachable!(),
                }
            },
            _ => todo!(),
        }
    }
    fn lift_pop(&self,
                size: usize,
                reg_offset: u8,
                helper_stub: &FunctionValue) {
        let vsp = get_param_vsp(helper_stub);
        let vm_regs = get_param_vm_regs(helper_stub);
        let i64_type = self.context.i64_type();

        let register_number = reg_offset / 8;
        let intra_register_offset = reg_offset % 8;

        let select_vm_reg = unsafe {
            self.builder.build_gep(vm_regs,
                                   &[i64_type.const_int(register_number as _, false)],
                                   "vm_reg")
        };

        match size {
            8 => {
                assert!(intra_register_offset == 0);

                let sem_pop_vmreg64 = self.get_semantic("SEM_POP_VMREG_64");

                self.builder
                    .build_call(sem_pop_vmreg64, &[vsp.into(), select_vm_reg.into()], "");
            },
            4 => {
                assert!(intra_register_offset == 4 || intra_register_offset == 0);
                match intra_register_offset {
                    0 => {
                        let sem_pop_vmreg32_low = self.get_semantic("SEM_POP_VMREG_32_LOW");

                        self.builder.build_call(sem_pop_vmreg32_low,
                                                &[vsp.into(), select_vm_reg.into()],
                                                "");
                    },
                    4 => {
                        let sem_pop_vmreg32_high = self.get_semantic("SEM_POP_VMREG_32_HIGH");

                        self.builder.build_call(sem_pop_vmreg32_high,
                                                &[vsp.into(), select_vm_reg.into()],
                                                "");
                    },
                    _ => unreachable!(),
                }
            },

            2 => match intra_register_offset {
                0 => {
                    let sem_pop_vmreg16_lowlow = self.get_semantic("SEM_POP_VMREG_16_LOWLOW");

                    self.builder
                        .build_call(sem_pop_vmreg16_lowlow, &[vsp.into(), vm_regs.into()], "");
                },
                2 => {
                    let sem_pop_vmreg16_lowhigh = self.get_semantic("SEM_POP_VMREG_16_LOWHIGH");

                    self.builder
                        .build_call(sem_pop_vmreg16_lowhigh, &[vsp.into(), vm_regs.into()], "");
                },
                4 => {
                    let sem_pop_vmreg16_highlow = self.get_semantic("SEM_POP_VMREG_16_HIGHLOW");

                    self.builder
                        .build_call(sem_pop_vmreg16_highlow, &[vsp.into(), vm_regs.into()], "");
                },
                6 => {
                    let sem_pop_vmreg16_highhigh = self.get_semantic("SEM_POP_VMREG_16_HIGHHIGH");

                    self.builder
                        .build_call(sem_pop_vmreg16_highhigh, &[vsp.into(), vm_regs.into()], "");
                },
                _ => unreachable!(),
            },

            1 => {
                assert!(intra_register_offset == 1 || intra_register_offset == 0);
                match intra_register_offset {
                    0 => {
                        let sem_pop_vmreg8_low = self.get_semantic("SEM_POP_VMREG_8_LOW");

                        self.builder.build_call(sem_pop_vmreg8_low,
                                                &[vsp.into(), select_vm_reg.into()],
                                                "");
                    },
                    1 => {
                        let sem_pop_vmreg8_high = self.get_semantic("SEM_POP_VMREG_8_HIGH");

                        self.builder.build_call(sem_pop_vmreg8_high,
                                                &[vsp.into(), select_vm_reg.into()],
                                                "");
                    },
                    _ => unreachable!(),
                }
            },
            _ => todo!(),
        }
    }
    fn get_semantic(&self,
                    name: &str)
                    -> CallableValue {
        let global_value = self.module
                               .borrow()
                               .get_global(name)
                               .unwrap_or_else(|| panic!("Could not find SEMANTIC {}", name));
        let sem_pointer = self.builder
                              .build_load(global_value.as_pointer_value(), "")
                              .into_pointer_value();

        CallableValue::try_from(sem_pointer).unwrap()
    }

    fn lift_vm_exit(&self,
                    vm_context: &VmContext,
                    stub_function: &FunctionValue) {
        let vsp = get_param_vsp(stub_function);
        let vip = get_param_vip(stub_function);

        for reg in vm_context.push_order.iter().rev() {
            let sem_push_reg64 = self.get_semantic("SEM_POP_REG_64");
            let reg_ptr = get_param_from_reg(reg, stub_function);
            self.builder
                .build_call(sem_push_reg64, &[vsp.into(), reg_ptr.into()], "");
        }

        let exit_semantic = self.get_semantic("SEM_EXIT");
        self.builder
            .build_call(exit_semantic, &[vsp.into(), vip.into()], "");
    }

    fn lift_vm_entry(&self,
                     vm_context: &VmContext,
                     stub_function: &FunctionValue) {
        let i64_type = self.context.i64_type();
        let vsp = get_param_vsp(stub_function);

        // This type does not implement clone that's the reason for resolving it three
        // times :) Yes this is fucking retarded :)
        let sem_push_imm64 = self.get_semantic("SEM_PUSH_IMM_64");
        let pushed_key = i64_type.const_int(vm_context.pushed_val, false);

        self.builder
            .build_call(sem_push_imm64, &[vsp.into(), pushed_key.into()], "");

        // This type does not implement clone that's the reason for resolving it three
        // times :)
        let sem_push_imm64 = self.get_semantic("SEM_PUSH_IMM_64");

        let ret_addr = i64_type.const_int(vm_context.vm_call_address + 10, false);
        let reloc = i64_type.const_int(vm_context.reloc_value, false);

        self.builder
            .build_call(sem_push_imm64, &[vsp.into(), ret_addr.into()], "");

        for reg in vm_context.push_order.iter() {
            let sem_push_reg64 = self.get_semantic("SEM_PUSH_REG_64");
            let reg_ptr = get_param_from_reg(reg, stub_function);
            let reg_value = self.builder.build_load(reg_ptr, "");
            self.builder
                .build_call(sem_push_reg64, &[vsp.into(), reg_value.into()], "");
        }

        // This type does not implement clone that's the reason for resolving it three
        // times :)
        let sem_push_imm64 = self.get_semantic("SEM_PUSH_IMM_64");
        self.builder
            .build_call(sem_push_imm64, &[vsp.into(), reloc.into()], "");
    }

    fn lift_into_helper_stub(&self,
                             vm_context: &VmContext,
                             handlers: &[(u64, HandlerVmInstruction, u64)],
                             helper_stub: &FunctionValue) {
        let entry_bb = helper_stub.get_basic_blocks()[0];
        let first_instruction = entry_bb.get_first_instruction().unwrap();
        self.builder.position_before(&first_instruction);

        self.lift_vm_entry(vm_context, helper_stub);

        for (_, handler, _) in handlers.iter() {
            self.lift_vm_instruction(vm_context, handler, helper_stub);
        }
    }

    pub fn create_helper_function(&self,
                                  control_flow_graph: &GraphMap<u64, (), petgraph::Directed>,
                                  start_vip: u64) {
        let helper_function_def = self.module
                                      .borrow()
                                      .get_function("HelperFunction")
                                      .expect("Could not find HelperFunction in llvm ir file");

        let llvm_lifetime_start_p0i8 =
            self.module
                .borrow()
                .get_function("llvm.lifetime.start.p0i8")
                .expect("Could not find llvm.lifetime.start.p0i8 in llvm ir file");

        let llvm_memset_p0i8_i64 =
            self.module
                .borrow()
                .get_function("llvm.memset.p0i8.i64")
                .expect("Could not find llvm.memset.p0i8.i64 in llvm ir file");

        let helper_function_type = helper_function_def.get_type();

        let helper_function = self.module
                                  .borrow()
                                  .add_function(&format!("helperfunction_{:x}", start_vip),
                                                helper_function_type,
                                                None);
        let param_names = ["rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp", "r8", "r9",
                           "r10", "r11", "r12", "r13", "r14", "r15", "flags", "KEY_STUB",
                           "RET_ADDR", "REL_ADDR"];

        for (i, (&name, param)) in
            std::iter::zip(param_names.iter(), helper_function.get_param_iter()).enumerate()
        {
            param.set_name(name);

            if name != "KEY_STUB" && name != "RET_ADDR" && name != "REL_ADDR" {
                helper_function.add_attribute(AttributeLoc::Param(i as _), self.context.create_enum_attribute(Attribute::get_named_enum_kind_id("noalias"), 0));
            }
        }

        // Cloning is all kinds of fucked with the rust lib so it is what it is
        let entry_bb = self.context.append_basic_block(helper_function, "entry");
        self.builder.position_at_end(entry_bb);

        let i64_type = self.context.i64_type();
        let i8_type = self.context.i8_type();
        let bool_type = self.context.bool_type();

        let virtual_register_type = self.module
                                        .borrow()
                                        .get_struct_type("struct.VirtualRegister")
                                        .unwrap();
        let virtual_register_array_type = virtual_register_type.array_type(30);

        let vmregs = self.builder
                         .build_alloca(virtual_register_array_type, "vmregs");

        let i64_array_type = i64_type.array_type(30);
        let slots = self.builder.build_alloca(i64_array_type, "slots");

        let vip = self.builder.build_alloca(i64_type, "vip");

        let t0 = self.builder
                     .build_bitcast(vmregs, i8_type.ptr_type(inkwell::AddressSpace::Generic), "");

        self.builder.build_call(llvm_lifetime_start_p0i8,
                                &[i64_type.const_int(240, false).into(), t0.into()],
                                "");
        self.builder.build_call(llvm_memset_p0i8_i64,
                                &[t0.into(),
                                  i8_type.const_zero().into(),
                                  i64_type.const_int(240, false).into(),
                                  bool_type.const_zero().into()],
                                "");

        let t1 = self.builder
                     .build_bitcast(slots, i8_type.ptr_type(inkwell::AddressSpace::Generic), "");

        self.builder.build_call(llvm_lifetime_start_p0i8,
                                &[i64_type.const_int(240, false).into(), t1.into()],
                                "");
        self.builder.build_call(llvm_memset_p0i8_i64,
                                &[t1.into(),
                                  i8_type.const_zero().into(),
                                  i64_type.const_int(240, false).into(),
                                  bool_type.const_zero().into()],
                                "");

        let t2 = self.builder
                     .build_bitcast(vip, i8_type.ptr_type(inkwell::AddressSpace::Generic), "");

        self.builder.build_call(llvm_lifetime_start_p0i8,
                                &[i64_type.const_int(8, false).into(), t2.into()],
                                "");

        let start_vip_llvm = i64_type.const_int(start_vip, false);
        self.builder.build_store(vip, start_vip_llvm);

        let array_decay = unsafe {
            self.builder.build_gep(vmregs,
                                   &[i64_type.const_zero(), i64_type.const_zero()],
                                   "arraydecay")
        };
        let array_decay1 = unsafe {
            self.builder.build_gep(slots,
                                   &[i64_type.const_zero(), i64_type.const_zero()],
                                   "arraydecay")
        };

        let mut bbs_map = HashMap::new();

        for node in control_flow_graph.nodes() {
            let stub_bb = self.context
                              .append_basic_block(helper_function, &format!("stub_{:x}", node));
            bbs_map.insert(node, stub_bb);
        }

        self.builder.build_unconditional_branch(bbs_map[&start_vip]);

        for node in control_flow_graph.nodes() {
            self.lift_bb_stub(control_flow_graph,
                              &helper_function,
                              &bbs_map,
                              node,
                              vip,
                              array_decay,
                              array_decay1,
                              t0,
                              t1,
                              t2);
        }

        assert!(helper_function.verify(true));
    }

    fn lift_bb_stub(&self,
                    control_flow_graph: &GraphMap<u64, (), petgraph::Directed>,
                    helper_function: &FunctionValue,
                    bbs_map: &HashMap<u64, BasicBlock>,
                    vip: u64,
                    vip_arg: PointerValue,
                    array_decay: PointerValue,
                    array_decay1: PointerValue,
                    t0: BasicValueEnum,
                    t1: BasicValueEnum,
                    t2: BasicValueEnum) {
        let i64_type = self.context.i64_type();

        println!("Getting helper stub -> helperstub_{:x}", vip);
        let helper_stub = self.module
                              .borrow()
                              .get_function(&format!("helperstub_{:x}", vip))
                              .unwrap();

        self.builder.position_at_end(bbs_map[&vip]);

        let call = self.builder.build_call(helper_stub,
                                           &[helper_function.get_nth_param(0).unwrap().into(),
                                             helper_function.get_nth_param(1).unwrap().into(),
                                             helper_function.get_nth_param(2).unwrap().into(),
                                             helper_function.get_nth_param(3).unwrap().into(),
                                             helper_function.get_nth_param(4).unwrap().into(),
                                             helper_function.get_nth_param(5).unwrap().into(),
                                             helper_function.get_nth_param(6).unwrap().into(),
                                             helper_function.get_nth_param(7).unwrap().into(),
                                             helper_function.get_nth_param(8).unwrap().into(),
                                             helper_function.get_nth_param(9).unwrap().into(),
                                             helper_function.get_nth_param(10).unwrap().into(),
                                             helper_function.get_nth_param(11).unwrap().into(),
                                             helper_function.get_nth_param(12).unwrap().into(),
                                             helper_function.get_nth_param(13).unwrap().into(),
                                             helper_function.get_nth_param(14).unwrap().into(),
                                             helper_function.get_nth_param(15).unwrap().into(),
                                             helper_function.get_nth_param(16).unwrap().into(),
                                             helper_function.get_nth_param(17).unwrap().into(),
                                             helper_function.get_nth_param(18).unwrap().into(),
                                             i64_type.const_int(0, false).into(),
                                             helper_function.get_nth_param(7).unwrap().into(),
                                             vip_arg.into(),
                                             array_decay.into(),
                                             array_decay1.into()],
                                           "call");
        let successors = control_flow_graph.edges_directed(vip, petgraph::EdgeDirection::Outgoing)
                                           .map(|(_, target, _)| target)
                                           .collect::<Vec<u64>>();

        match successors.len() {
            0 => {
                let llvm_lifetime_end_p0i8 =
                    self.module
                        .borrow()
                        .get_function("llvm.lifetime.end.p0i8")
                        .expect("Could not find llvm.lifetime.end.p0i8 in llvm ir file");

                let undef = self.module.borrow().get_global("__undef").unwrap();
                let t3 = self.builder.build_load(undef.as_pointer_value(), "");

                self.builder.build_store(helper_function.get_nth_param(16)
                                                        .unwrap()
                                                        .into_pointer_value(),
                                         t3);
                self.builder.build_call(llvm_lifetime_end_p0i8,
                                        &[i64_type.const_int(8, false).into(), t2.into()],
                                        "");
                self.builder.build_call(llvm_lifetime_end_p0i8,
                                        &[i64_type.const_int(240, false).into(), t1.into()],
                                        "");
                self.builder.build_call(llvm_lifetime_end_p0i8,
                                        &[i64_type.const_int(240, false).into(), t0.into()],
                                        "");

                self.builder
                    .build_return(Some(&call.try_as_basic_value().unwrap_left()));
            },
            1 => {
                let destination_vip = successors[0];
                let destination_bb = bbs_map[&destination_vip];
                self.builder.build_unconditional_branch(destination_bb);
            },
            2 => {
                let vip_value = self.builder.build_load(vip_arg, "vip_value");

                let branch_target1 = successors[0];
                let branch_target2 = successors[1];

                let llvm_branch_target1 = i64_type.const_int(branch_target1, false);

                let branch_selector = self.builder.build_int_compare(inkwell::IntPredicate::EQ,
                                                                     vip_value.into_int_value(),
                                                                     llvm_branch_target1,
                                                                     "eq_br1");

                let branch1 = bbs_map[&branch_target1];
                let branch2 = bbs_map[&branch_target2];

                self.builder
                    .build_conditional_branch(branch_selector, branch1, branch2);
            },
            _ => {
                todo!();
            },
        }
    }

    pub fn create_helper_slicevpc(&self,
                                  vips: &[u64]) {
        let start_vip = vips[0];

        let helper_function_def = self.module
                                      .borrow()
                                      .get_function("HelperFunction")
                                      .expect("Could not find HelperFunction in llvm ir file");

        let llvm_lifetime_start_p0i8 =
            self.module
                .borrow()
                .get_function("llvm.lifetime.start.p0i8")
                .expect("Could not find llvm.lifetime.start.p0i8 in llvm ir file");

        let llvm_lifetime_end_p0i8 =
            self.module
                .borrow()
                .get_function("llvm.lifetime.end.p0i8")
                .expect("Could not find llvm.lifetime.end.p0i8 in llvm ir file");

        let llvm_memset_p0i8_i64 =
            self.module
                .borrow()
                .get_function("llvm.memset.p0i8.i64")
                .expect("Could not find llvm.memset.p0i8.i64 in llvm ir file");

        let helper_function_type = helper_function_def.get_type();

        let helper_slicevpc = self.module
                                  .borrow()
                                  .add_function("helperslicevpc", helper_function_type, None);
        let param_names = ["rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp", "r8", "r9",
                           "r10", "r11", "r12", "r13", "r14", "r15", "flags", "KEY_STUB",
                           "RET_ADDR", "REL_ADDR"];

        for (i, (&name, param)) in
            std::iter::zip(param_names.iter(), helper_slicevpc.get_param_iter()).enumerate()
        {
            param.set_name(name);

            if name != "KEY_STUB" && name != "RET_ADDR" && name != "REL_ADDR" {
                helper_slicevpc.add_attribute(AttributeLoc::Param(i as _), self.context.create_enum_attribute(Attribute::get_named_enum_kind_id("noalias"), 0));
            }
        }

        // Cloning is all kinds of fucked with the rust lib so it is what it is
        let entry_bb = self.context.append_basic_block(helper_slicevpc, "entry");
        self.builder.position_at_end(entry_bb);

        let i64_type = self.context.i64_type();
        let i8_type = self.context.i8_type();
        let bool_type = self.context.bool_type();

        let virtual_register_type = self.module
                                        .borrow()
                                        .get_struct_type("struct.VirtualRegister")
                                        .unwrap();
        let virtual_register_array_type = virtual_register_type.array_type(30);

        let vmregs = self.builder
                         .build_alloca(virtual_register_array_type, "vmregs");

        let i64_array_type = i64_type.array_type(30);
        let slots = self.builder.build_alloca(i64_array_type, "slots");

        let vip = self.builder.build_alloca(i64_type, "vip");

        let t0 = self.builder
                     .build_bitcast(vmregs, i8_type.ptr_type(inkwell::AddressSpace::Generic), "");

        self.builder.build_call(llvm_lifetime_start_p0i8,
                                &[i64_type.const_int(240, false).into(), t0.into()],
                                "");
        self.builder.build_call(llvm_memset_p0i8_i64,
                                &[t0.into(),
                                  i8_type.const_zero().into(),
                                  i64_type.const_int(240, false).into(),
                                  bool_type.const_zero().into()],
                                "");

        let t1 = self.builder
                     .build_bitcast(slots, i8_type.ptr_type(inkwell::AddressSpace::Generic), "");

        self.builder.build_call(llvm_lifetime_start_p0i8,
                                &[i64_type.const_int(240, false).into(), t1.into()],
                                "");
        self.builder.build_call(llvm_memset_p0i8_i64,
                                &[t1.into(),
                                  i8_type.const_zero().into(),
                                  i64_type.const_int(240, false).into(),
                                  bool_type.const_zero().into()],
                                "");

        let t2 = self.builder
                     .build_bitcast(vip, i8_type.ptr_type(inkwell::AddressSpace::Generic), "");

        self.builder.build_call(llvm_lifetime_start_p0i8,
                                &[i64_type.const_int(8, false).into(), t2.into()],
                                "");

        let start_vip_llvm = i64_type.const_int(start_vip, false);
        self.builder.build_store(vip, start_vip_llvm);

        let array_decay = unsafe {
            self.builder.build_gep(vmregs,
                                   &[i64_type.const_zero(), i64_type.const_zero()],
                                   "arraydecay")
        };
        let array_decay1 = unsafe {
            self.builder.build_gep(slots,
                                   &[i64_type.const_zero(), i64_type.const_zero()],
                                   "arraydecay")
        };

        let mut call = None;
        for stub_vip in vips.iter().rev() {
            let helper_stub = self.module
                                  .borrow()
                                  .get_function(&format!("helperstub_{:x}", stub_vip))
                                  .unwrap();

            let temp =
                self.builder.build_call(helper_stub,
                                        &[helper_slicevpc.get_nth_param(0).unwrap().into(),
                                          helper_slicevpc.get_nth_param(1).unwrap().into(),
                                          helper_slicevpc.get_nth_param(2).unwrap().into(),
                                          helper_slicevpc.get_nth_param(3).unwrap().into(),
                                          helper_slicevpc.get_nth_param(4).unwrap().into(),
                                          helper_slicevpc.get_nth_param(5).unwrap().into(),
                                          helper_slicevpc.get_nth_param(6).unwrap().into(),
                                          helper_slicevpc.get_nth_param(7).unwrap().into(),
                                          helper_slicevpc.get_nth_param(8).unwrap().into(),
                                          helper_slicevpc.get_nth_param(9).unwrap().into(),
                                          helper_slicevpc.get_nth_param(10).unwrap().into(),
                                          helper_slicevpc.get_nth_param(11).unwrap().into(),
                                          helper_slicevpc.get_nth_param(12).unwrap().into(),
                                          helper_slicevpc.get_nth_param(13).unwrap().into(),
                                          helper_slicevpc.get_nth_param(14).unwrap().into(),
                                          helper_slicevpc.get_nth_param(15).unwrap().into(),
                                          helper_slicevpc.get_nth_param(16).unwrap().into(),
                                          helper_slicevpc.get_nth_param(17).unwrap().into(),
                                          helper_slicevpc.get_nth_param(18).unwrap().into(),
                                          i64_type.const_int(0, false).into(),
                                          helper_slicevpc.get_nth_param(7).unwrap().into(),
                                          vip.into(),
                                          array_decay.into(),
                                          array_decay1.into()],
                                        "call");

            call = Some(temp);
        }

        let undef = self.module.borrow().get_global("__undef").unwrap();
        let t3 = self.builder.build_load(undef.as_pointer_value(), "");

        self.builder.build_store(helper_slicevpc.get_nth_param(16)
                                                .unwrap()
                                                .into_pointer_value(),
                                 t3);
        self.builder.build_call(llvm_lifetime_end_p0i8,
                                &[i64_type.const_int(8, false).into(), t2.into()],
                                "");
        self.builder.build_call(llvm_lifetime_end_p0i8,
                                &[i64_type.const_int(240, false).into(), t1.into()],
                                "");
        self.builder.build_call(llvm_lifetime_end_p0i8,
                                &[i64_type.const_int(240, false).into(), t0.into()],
                                "");

        self.builder
            .build_return(Some(&call.unwrap().try_as_basic_value().unwrap_left()));

        assert!(helper_slicevpc.verify(true));
    }
}

fn get_param_from_reg<'a>(register: &Registers,
                          helper_stub: &FunctionValue<'a>)
                          -> PointerValue<'a> {
    helper_stub.get_nth_param(register.to_arg_index() as _)
               .unwrap()
               .into_pointer_value()
}

#[allow(dead_code)]
fn get_param_reloc<'a>(helper_stub: &FunctionValue<'a>) -> BasicValueEnum<'a> {
    helper_stub.get_nth_param(19).unwrap()
}

fn get_param_vsp<'a>(helper_stub: &FunctionValue<'a>) -> PointerValue<'a> {
    helper_stub.get_nth_param(20).unwrap().into_pointer_value()
}

fn get_param_vip<'a>(helper_stub: &FunctionValue<'a>) -> PointerValue<'a> {
    helper_stub.get_nth_param(21).unwrap().into_pointer_value()
}

fn get_param_vm_regs<'a>(helper_stub: &FunctionValue<'a>) -> PointerValue<'a> {
    helper_stub.get_nth_param(22).unwrap().into_pointer_value()
}

#[allow(dead_code)]
fn get_operand_names(instruction: &InstructionValue) -> Vec<String> {
    let mut return_value = Vec::new();
    let num_operands = instruction.get_num_operands();

    for i in 0 .. num_operands {
        let operand = instruction.get_operand(i).unwrap();
        assert!(operand.is_left());

        let operand = operand.left().unwrap();

        if operand.is_int_value() {
            let temp = operand.into_int_value();
            let name = temp.get_name();
            return_value.push(name.to_str().unwrap().to_owned());
            continue;
        }
        if operand.is_array_value() {
            let temp = operand.into_array_value();
            let name = temp.get_name();
            return_value.push(name.to_str().unwrap().to_owned());
            continue;
        }
        if operand.is_float_value() {
            let temp = operand.into_float_value();
            let name = temp.get_name();
            return_value.push(name.to_str().unwrap().to_owned());
            continue;
        }
        if operand.is_struct_value() {
            let temp = operand.into_struct_value();
            let name = temp.get_name();
            return_value.push(name.to_str().unwrap().to_owned());
            continue;
        }
        if operand.is_pointer_value() {
            let temp = operand.into_pointer_value();
            let name = temp.get_name();
            return_value.push(name.to_str().unwrap().to_owned());
            continue;
        }
        if operand.is_vector_value() {
            let temp = operand.into_vector_value();
            let name = temp.get_name();
            return_value.push(name.to_str().unwrap().to_owned());
            continue;
        }
    }

    return_value
}
