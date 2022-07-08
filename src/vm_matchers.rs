use std::fmt::Display;

use iced_x86::{Code, Instruction, Register};

use crate::{
    match_assembly::*,
    util::check_full_reg_written,
    vm_handler::{Registers, VmContext, VmHandler, VmRegisterAllocation},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HandlerClass {
    ByteOperand,
    WordOperand,
    DwordOperand,
    QwordOperand,
    NoOperand,
    UnconditionalBranch,
    NoVipChange,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HandlerVmInstruction {
    /// Size in bytes and reg offset in register file
    Pop(usize, u8),
    Push(usize, u8),
    PushImm64(u64),
    PushImm32(u32),
    PushImm16(u16),
    PushImm8(u8),
    PushVsp(usize),
    PopVsp(usize),
    Add(usize),
    Mul(usize),
    Imul(usize),
    Shr(usize),
    Shl(usize),
    Shrd(usize),
    Shld(usize),
    Nand(usize),
    Nor(usize),
    Fetch(usize),
    Store(usize),
    PushCr0,
    Nop,
    VmExit,
    JumpDecVspChange,
    JumpIncVspChange,
    JumpDecVspXchng,
    JumpIncVspXchng,
    JumpDec,
    JumpInc,
    UnknownByteOperand,
    UnknownWordOperand,
    UnknownDwordOperand,
    UnknownQwordOperand,
    UnknownNoOperand,
    UnknownNoVipChange,
    Unknown,
}

impl Display for HandlerVmInstruction {
    fn fmt(&self,
           f: &mut std::fmt::Formatter<'_>)
           -> std::fmt::Result {
        /// Local function for fomatting registers
        fn format_reg_offset(reg_offset: u8,
                             size: usize)
                             -> String {
            let register_number = reg_offset / 8;
            let inner_reg_offset = reg_offset % 8;

            match size {
                8 => {
                    format!("r{}", register_number)
                },
                4 => match inner_reg_offset {
                    0 => format!("r{}_dword_0", register_number),
                    4 => format!("r{}_dword_1", register_number),
                    _ => unimplemented!(),
                },
                2 => match inner_reg_offset {
                    0 => format!("r{}_word_0", register_number),
                    2 => format!("r{}_word_1", register_number),
                    4 => format!("r{}_word_2", register_number),
                    6 => format!("r{}_word_3", register_number),
                    _ => {
                        dbg!(inner_reg_offset);
                        unimplemented!();
                    },
                },
                1 => match inner_reg_offset {
                    0 => format!("r{}_byte_0", register_number),
                    1 => format!("r{}_byte_1", register_number),
                    _ => unimplemented!(),
                },
                _ => unimplemented!("Size -> not implemented yet {}", size),
            }
        }

        match self {
            HandlerVmInstruction::Pop(size, reg_offset) => write!(f,
                                                                  "pop{} {}",
                                                                  size * 8,
                                                                  format_reg_offset(*reg_offset,
                                                                                    *size)),
            HandlerVmInstruction::Push(size, reg_offset) => write!(f,
                                                                   "push{} {}",
                                                                   size * 8,
                                                                   format_reg_offset(*reg_offset,
                                                                                     *size)),
            HandlerVmInstruction::PushImm64(imm64) => write!(f, "push_imm64 {:#x}", imm64),
            HandlerVmInstruction::PushImm32(imm32) => write!(f, "push_imm32 {:#x}", imm32),
            HandlerVmInstruction::PushImm16(imm16) => write!(f, "push_imm16 {:#x}", imm16),
            HandlerVmInstruction::PushImm8(imm8) => write!(f, "push_imm8 {:#x}", imm8),
            HandlerVmInstruction::PushVsp(size) => write!(f, "pushvsp{}", size * 8),
            HandlerVmInstruction::PopVsp(size) => write!(f, "popvsp{}", size * 8),
            HandlerVmInstruction::Add(size) => write!(f, "add{}", size * 8),
            HandlerVmInstruction::Mul(size) => write!(f, "mul{}", size * 8),
            HandlerVmInstruction::Imul(size) => write!(f, "imul{}", size * 8),
            HandlerVmInstruction::Shrd(size) => write!(f, "shrd{}", size * 8),
            HandlerVmInstruction::Shld(size) => write!(f, "shld{}", size * 8),
            HandlerVmInstruction::Shr(size) => write!(f, "shr{}", size * 8),
            HandlerVmInstruction::Shl(size) => write!(f, "shl{}", size * 8),
            HandlerVmInstruction::Nand(size) => write!(f, "nand{}", size * 8),
            HandlerVmInstruction::Nor(size) => write!(f, "nor{}", size * 8),
            HandlerVmInstruction::Fetch(size) => write!(f, "fetch{}", size * 8),
            HandlerVmInstruction::Store(size) => write!(f, "store{}", size * 8),
            HandlerVmInstruction::PushCr0 => write!(f, "push_cr0"),
            HandlerVmInstruction::Nop => write!(f, "nop"),
            HandlerVmInstruction::VmExit => write!(f, "vm_exit"),
            HandlerVmInstruction::JumpDecVspXchng => write!(f, "jump_dec_vsp_xchng"),
            HandlerVmInstruction::JumpIncVspXchng => write!(f, "jump_inc_vsp_xchng"),
            HandlerVmInstruction::JumpDecVspChange => write!(f, "jump_dec_vsp_change"),
            HandlerVmInstruction::JumpIncVspChange => write!(f, "jump_inc_vsp_change"),
            HandlerVmInstruction::JumpDec => write!(f, "jump_dec"),
            HandlerVmInstruction::JumpInc => write!(f, "jump_inc"),
            HandlerVmInstruction::UnknownByteOperand => {
                write!(f, "[unknown byte operand instruction]")
            },
            HandlerVmInstruction::UnknownWordOperand => {
                write!(f, "[unknown word operand instruction]")
            },
            HandlerVmInstruction::UnknownDwordOperand => {
                write!(f, "[unknown dword operand instruction]")
            },
            HandlerVmInstruction::UnknownQwordOperand => {
                write!(f, "[unknown qword operand instruction]")
            },
            HandlerVmInstruction::UnknownNoOperand => write!(f, "[unknown no operand instruction]"),
            HandlerVmInstruction::UnknownNoVipChange => {
                write!(f, "[unknown no vip change instruction]")
            },
            HandlerVmInstruction::Unknown => write!(f, "[unknown instruction]"),
        }
    }
}

impl VmHandler {
    /// Classify the handler based on the class of access to the vip register
    pub fn match_handler_class(&self,
                               reg_allocation: &VmRegisterAllocation)
                               -> HandlerClass {
        // Create an iterator over the instructions of the handler
        let instruction_iter = self.instructions.iter();

        // Collect all the mov accesses to the vip register
        let vip_modification_vec =
            instruction_iter.clone()
                            .filter(|insn| check_full_reg_written(insn, reg_allocation.vip.into()))
                            .filter(|insn| insn.code() == Code::Mov_r64_rm64)
                            .collect::<Vec<_>>();

        // These registers are used in the stack relocation code of some handlers so
        // they are special
        if (reg_allocation.vip != Registers::Rsi &&
            reg_allocation.vip != Registers::Rdi &&
            !vip_modification_vec.is_empty()) ||
           (vip_modification_vec.len() >= 2)
        {
            return HandlerClass::UnconditionalBranch;
        }

        // Collect all instructions that advance the vip and get their immediate values
        let vip_update_vec =
            instruction_iter.filter(|insn| check_full_reg_written(insn, reg_allocation.vip.into()))
                            .filter(|insn| {
                                insn.code() == Code::Add_rm64_imm32 ||
                                insn.code() == Code::Sub_rm64_imm32
                            })
                            .map(|insn| insn.immediate32())
                            .collect::<Vec<_>>();

        // Match the vip offsets to a handler class
        match vip_update_vec.as_slice() {
            &[] => HandlerClass::NoVipChange,
            &[4] => HandlerClass::NoOperand,
            &[8, 4] => HandlerClass::QwordOperand,
            &[4, 4] => HandlerClass::DwordOperand,
            &[2, 4] => HandlerClass::WordOperand,
            &[1, 4] => HandlerClass::ByteOperand,
            slice => {
                panic!("Unimplemented handler class with slice {:?}", slice)
            },
        }
    }

    /// Function for matching handlers of the UnconditionalBranch class
    pub fn match_branch_instructions(&self,
                                     vm_context: &VmContext)
                                     -> HandlerVmInstruction {
        if vm_match_vm_exit(self, &vm_context.register_allocation) {
            return HandlerVmInstruction::VmExit;
        }

        if vm_match_jmp_dec_vsp_change(self, vm_context) {
            return HandlerVmInstruction::JumpDecVspChange;
        }

        if vm_match_jmp_inc_vsp_change(self, vm_context) {
            return HandlerVmInstruction::JumpIncVspChange;
        }

        if vm_match_jmp_dec_vsp_xchng(self, vm_context) {
            return HandlerVmInstruction::JumpDecVspXchng;
        }

        if vm_match_jmp_inc_vsp_xchng(self, vm_context) {
            return HandlerVmInstruction::JumpIncVspXchng;
        }

        if vm_match_jmp_dec(self, vm_context) {
            return HandlerVmInstruction::JumpDec;
        }

        if vm_match_jmp_inc(self, vm_context) {
            return HandlerVmInstruction::JumpInc;
        }

        HandlerVmInstruction::Unknown
    }

    /// Function for mathing the handlers of the NoVipChange class
    pub fn match_no_vip_change_instructions(&self,
                                            vm_context: &VmContext)
                                            -> HandlerVmInstruction {
        if vm_match_vm_exit(self, &vm_context.register_allocation) {
            return HandlerVmInstruction::VmExit;
        }

        if vm_match_jmp_dec_vsp_change(self, vm_context) {
            return HandlerVmInstruction::JumpDecVspChange;
        }

        if vm_match_jmp_inc_vsp_change(self, vm_context) {
            return HandlerVmInstruction::JumpIncVspChange;
        }

        if vm_match_jmp_dec_vsp_xchng(self, vm_context) {
            return HandlerVmInstruction::JumpDecVspXchng;
        }

        if vm_match_jmp_inc_vsp_xchng(self, vm_context) {
            return HandlerVmInstruction::JumpIncVspXchng;
        }

        if vm_match_jmp_dec(self, vm_context) {
            return HandlerVmInstruction::JumpDec;
        }

        if vm_match_jmp_inc(self, vm_context) {
            return HandlerVmInstruction::JumpInc;
        }

        HandlerVmInstruction::UnknownNoVipChange
    }

    /// Function for mathing the handlers of the ByteOperand class
    pub fn match_byte_operand_instructions(&self,
                                           reg_allocation: &VmRegisterAllocation,
                                           byte_operand: u8)
                                           -> HandlerVmInstruction {
        if vm_match_push_imm8(self, reg_allocation) {
            return HandlerVmInstruction::PushImm8(byte_operand);
        }

        if let Some(size) = vm_match_vm_reg_pop(self, reg_allocation) {
            return HandlerVmInstruction::Pop(size, byte_operand);
        }

        if let Some(size) = vm_match_vm_reg_pop_v2(self, reg_allocation) {
            return HandlerVmInstruction::Pop(size, byte_operand);
        }

        if let Some(size) = vm_match_vm_reg_push(self, reg_allocation) {
            return HandlerVmInstruction::Push(size, byte_operand);
        }

        HandlerVmInstruction::UnknownByteOperand
    }

    /// Function for mathing the handlers of the WordOperand class
    pub fn match_word_operand_instructions(&self,
                                           reg_allocation: &VmRegisterAllocation,
                                           word_operand: u16)
                                           -> HandlerVmInstruction {
        if vm_match_push_imm16(self, reg_allocation) {
            return HandlerVmInstruction::PushImm16(word_operand);
        }
        HandlerVmInstruction::UnknownWordOperand
    }

    /// Function for mathing the handlers of the DwordOperand class
    pub fn match_dword_operand_instructions(&self,
                                            reg_allocation: &VmRegisterAllocation,
                                            dword_operand: u32)
                                            -> HandlerVmInstruction {
        if vm_match_push_imm32(self, reg_allocation) {
            return HandlerVmInstruction::PushImm32(dword_operand);
        }
        HandlerVmInstruction::UnknownDwordOperand
    }

    /// Function for mathing the handlers of the QwordOperand class
    pub fn match_qword_operand_instructions(&self,
                                            reg_allocation: &VmRegisterAllocation,
                                            qword_operand: u64)
                                            -> HandlerVmInstruction {
        if vm_match_push_imm64(self, reg_allocation) {
            return HandlerVmInstruction::PushImm64(qword_operand);
        }
        HandlerVmInstruction::UnknownQwordOperand
    }

    /// Function for mathing the handlers of the NoOperand class
    pub fn match_no_operand_instructions(&self,
                                         vm_context: &VmContext,
                                         reg_allocation: &VmRegisterAllocation)
                                         -> HandlerVmInstruction {
        if let Some(size) = vm_match_push_vsp(self, reg_allocation) {
            return HandlerVmInstruction::PushVsp(size);
        }

        if vm_match_jmp_dec_vsp_change(self, vm_context) {
            return HandlerVmInstruction::JumpDecVspChange;
        }

        if vm_match_jmp_inc_vsp_change(self, vm_context) {
            return HandlerVmInstruction::JumpIncVspChange;
        }

        if vm_match_jmp_dec_vsp_xchng(self, vm_context) {
            return HandlerVmInstruction::JumpDecVspXchng;
        }

        if vm_match_jmp_inc_vsp_xchng(self, vm_context) {
            return HandlerVmInstruction::JumpIncVspXchng;
        }

        if vm_match_jmp_dec(self, vm_context) {
            return HandlerVmInstruction::JumpDec;
        }

        if vm_match_jmp_inc(self, vm_context) {
            return HandlerVmInstruction::JumpInc;
        }

        if let Some(size) = vm_match_add(self, reg_allocation) {
            return HandlerVmInstruction::Add(size);
        }

        if let Some(size) = vm_match_add_byte(self, reg_allocation) {
            return HandlerVmInstruction::Add(size);
        }

        if let Some(size) = vm_match_mul(self, reg_allocation) {
            return HandlerVmInstruction::Mul(size);
        }

        if let Some(size) = vm_match_imul(self, reg_allocation) {
            return HandlerVmInstruction::Imul(size);
        }

        if let Some(size) = vm_match_nand(self, reg_allocation) {
            return HandlerVmInstruction::Nand(size);
        }

        if let Some(size) = vm_match_nand_byte(self, reg_allocation) {
            return HandlerVmInstruction::Nand(size);
        }

        if let Some(size) = vm_match_nor(self, reg_allocation) {
            return HandlerVmInstruction::Nor(size);
        }

        if let Some(size) = vm_match_nor_byte(self, reg_allocation) {
            return HandlerVmInstruction::Nor(size);
        }

        if vm_match_pop_vsp_64(self, reg_allocation) {
            return HandlerVmInstruction::PopVsp(8);
        }

        if let Some(size) = vm_match_fetch(self, reg_allocation) {
            return HandlerVmInstruction::Fetch(size);
        }

        if let Some(size) = vm_match_fetch_byte(self, reg_allocation) {
            return HandlerVmInstruction::Fetch(size);
        }

        if let Some(size) = vm_match_store(self, reg_allocation) {
            return HandlerVmInstruction::Store(size);
        }

        if let Some(size) = vm_match_shr(self, reg_allocation) {
            return HandlerVmInstruction::Shr(size);
        }

        if let Some(size) = vm_match_shr_byte(self, reg_allocation) {
            return HandlerVmInstruction::Shr(size);
        }

        if let Some(size) = vm_match_shl(self, reg_allocation) {
            return HandlerVmInstruction::Shl(size);
        }

        if let Some(size) = vm_match_shl_byte(self, reg_allocation) {
            return HandlerVmInstruction::Shl(size);
        }

        if let Some(size) = vm_match_shrd(self, reg_allocation) {
            return HandlerVmInstruction::Shrd(size);
        }

        if let Some(size) = vm_match_shld(self, reg_allocation) {
            return HandlerVmInstruction::Shld(size);
        }

        if vm_match_nop(self) {
            return HandlerVmInstruction::Nop;
        }

        if vm_match_push_cr0(self) {
            return HandlerVmInstruction::PushCr0;
        }

        HandlerVmInstruction::UnknownNoOperand
    }
}

fn vm_match_jmp_dec(vm_handler: &VmHandler,
                    vm_context: &VmContext)
                    -> bool {
    let mut instruction_iter = vm_handler.instructions.iter();
    let mov_to_vip =
        instruction_iter.find(|insn| {
            match_fetch_reg_any_size(insn, vm_context.register_allocation.vsp.into()).is_some()
        });

    if mov_to_vip.is_none() {
        return false;
    }

    let new_vip = mov_to_vip.unwrap().op0_register().full_register();

    let add_vsp_instruction =
        instruction_iter.find(|insn| match_add_vsp_get_amount(insn, &vm_context.register_allocation).is_some());

    if add_vsp_instruction.is_none() {
        return false;
    }

    if add_vsp_instruction.unwrap().immediate32() != 8 {
        return false;
    }

    let mut cloned_iter = instruction_iter.clone();
    let mov_vip = cloned_iter.find(|insn| match_mov_reg_source(insn, new_vip));
    let new_vip = match mov_vip {
        Some(mov_vip) => {
            let potential_vip = mov_vip.op0_register().full_register();
            if cloned_iter.any(|insn| match_sub_reg_left(insn, potential_vip)) {
                new_vip
            } else {
                potential_vip
            }
        },
        None => new_vip,
    };

    let store_key_reg = instruction_iter.find(|insn| match_mov_reg_source(insn, new_vip));

    if store_key_reg.is_none() {
        return false;
    }

    instruction_iter.any(|insn| match_sub_reg_by_amount(insn, new_vip, 4))
}

fn vm_match_jmp_inc(vm_handler: &VmHandler,
                    vm_context: &VmContext)
                    -> bool {
    let mut instruction_iter = vm_handler.instructions.iter();
    let mov_to_vip =
        instruction_iter.find(|insn| {
            match_fetch_reg_any_size(insn, vm_context.register_allocation.vsp.into()).is_some()
        });

    if mov_to_vip.is_none() {
        return false;
    }

    let new_vip = mov_to_vip.unwrap().op0_register().full_register();

    let add_vsp_instruction =
        instruction_iter.find(|insn| match_add_vsp_get_amount(insn, &vm_context.register_allocation).is_some());

    if add_vsp_instruction.is_none() {
        return false;
    }

    if add_vsp_instruction.unwrap().immediate32() != 8 {
        return false;
    }

    let mut cloned_iter = instruction_iter.clone();
    let mov_vip = cloned_iter.find(|insn| match_mov_reg_source(insn, new_vip));
    let new_vip = match mov_vip {
        Some(mov_vip) => {
            let potential_vip = mov_vip.op0_register().full_register();
            if cloned_iter.any(|insn| match_sub_reg_left(insn, potential_vip)) {
                new_vip
            } else {
                potential_vip
            }
        },
        None => new_vip,
    };

    let store_key_reg = instruction_iter.find(|insn| match_mov_reg_source(insn, new_vip));

    if store_key_reg.is_none() {
        return false;
    }

    instruction_iter.any(|insn| match_add_reg_by_amount(insn, new_vip, 4))
}

fn vm_match_jmp_dec_vsp_change(vm_handler: &VmHandler,
                               vm_context: &VmContext)
                               -> bool {
    let mut instruction_iter = vm_handler.instructions.iter();
    let mov_to_vip =
        instruction_iter.find(|insn| {
            match_fetch_reg_any_size(insn, vm_context.register_allocation.vsp.into()).is_some()
        });

    if mov_to_vip.is_none() {
        return false;
    }

    let new_vip = mov_to_vip.unwrap().op0_register().full_register();

    let add_vsp_instruction =
        instruction_iter.find(|insn| match_add_vsp_get_amount(insn, &vm_context.register_allocation).is_some());

    if add_vsp_instruction.is_none() {
        return false;
    }

    if add_vsp_instruction.unwrap().immediate32() != 8 {
        return false;
    }

    let mut cloned_iter = instruction_iter.clone();
    let mov_vip = cloned_iter.find(|insn| match_mov_reg_source(insn, new_vip));
    let new_vip = match mov_vip {
        Some(mov_vip) => {
            let potential_vip = mov_vip.op0_register().full_register();
            if cloned_iter.any(|insn| match_sub_reg_left(insn, potential_vip)) {
                new_vip
            } else {
                potential_vip
            }
        },
        None => new_vip,
    };

    let _mov_vsp =
        instruction_iter.find(|insn| {
                            match_mov_reg_source(insn, vm_context.register_allocation.vsp.into())
                        });

    let store_key_reg = instruction_iter.find(|insn| match_mov_reg_source(insn, new_vip));

    if store_key_reg.is_none() {
        return false;
    }

    instruction_iter.any(|insn| match_sub_reg_by_amount(insn, new_vip, 4))
}

fn vm_match_jmp_inc_vsp_change(vm_handler: &VmHandler,
                               vm_context: &VmContext)
                               -> bool {
    let mut instruction_iter = vm_handler.instructions.iter();
    let mov_to_vip =
        instruction_iter.find(|insn| {
            match_fetch_reg_any_size(insn, vm_context.register_allocation.vsp.into()).is_some()
        });

    if mov_to_vip.is_none() {
        return false;
    }

    let new_vip = mov_to_vip.unwrap().op0_register().full_register();

    let add_vsp_instruction =
        instruction_iter.find(|insn| match_add_vsp_get_amount(insn, &vm_context.register_allocation).is_some());

    if add_vsp_instruction.is_none() {
        return false;
    }

    if add_vsp_instruction.unwrap().immediate32() != 8 {
        return false;
    }

    let mut cloned_iter = instruction_iter.clone();
    let mov_vip = cloned_iter.find(|insn| match_mov_reg_source(insn, new_vip));
    let new_vip = match mov_vip {
        Some(mov_vip) => {
            let potential_vip = mov_vip.op0_register().full_register();
            if cloned_iter.any(|insn| match_sub_reg_left(insn, potential_vip)) {
                new_vip
            } else {
                potential_vip
            }
        },
        None => new_vip,
    };

    let _mov_vsp =
        instruction_iter.find(|insn| {
                            match_mov_reg_source(insn, vm_context.register_allocation.vsp.into())
                        });

    let store_key_reg = instruction_iter.find(|insn| match_mov_reg_source(insn, new_vip));

    if store_key_reg.is_none() {
        return false;
    }

    instruction_iter.any(|insn| match_add_reg_by_amount(insn, new_vip, 4))
}

fn vm_match_jmp_dec_vsp_xchng(vm_handler: &VmHandler,
                              vm_context: &VmContext)
                              -> bool {
    let mut instruction_iter = vm_handler.instructions.iter();
    let mov_to_vip =
        instruction_iter.find(|insn| {
            match_fetch_reg_any_size(insn, vm_context.register_allocation.vsp.into()).is_some()
        });

    if mov_to_vip.is_none() {
        return false;
    }

    let new_vip = mov_to_vip.unwrap().op0_register().full_register();

    let add_vsp_instruction =
        instruction_iter.find(|insn| match_add_vsp_get_amount(insn, &vm_context.register_allocation).is_some());

    if add_vsp_instruction.is_none() {
        return false;
    }

    if add_vsp_instruction.unwrap().immediate32() != 8 {
        return false;
    }

    let xchng = instruction_iter.find(|insn| match_xchng_reg(insn, new_vip));

    let new_vip_reg;
    match xchng {
        Some(xchng_insn) => {
            if !(xchng_insn.op0_register() == new_vip &&
                 xchng_insn.op1_register() == vm_context.register_allocation.vsp.into()) &&
               !(xchng_insn.op1_register() == new_vip &&
                 xchng_insn.op0_register() == vm_context.register_allocation.vsp.into())
            {
                return false;
            } else {
                new_vip_reg = vm_context.register_allocation.vsp.into();
            }
        },
        None => return false,
    }

    let store_key_reg = instruction_iter.find(|insn| match_mov_reg_source(insn, new_vip_reg));

    if store_key_reg.is_none() {
        return false;
    }

    instruction_iter.any(|insn| match_sub_reg_by_amount(insn, new_vip_reg, 4))
}

fn vm_match_jmp_inc_vsp_xchng(vm_handler: &VmHandler,
                              vm_context: &VmContext)
                              -> bool {
    let mut instruction_iter = vm_handler.instructions.iter();
    let mov_to_vip =
        instruction_iter.find(|insn| {
            match_fetch_reg_any_size(insn, vm_context.register_allocation.vsp.into()).is_some()
        });

    if mov_to_vip.is_none() {
        return false;
    }

    let new_vip = mov_to_vip.unwrap().op0_register().full_register();

    let add_vsp_instruction =
        instruction_iter.find(|insn| match_add_vsp_get_amount(insn, &vm_context.register_allocation).is_some());

    if add_vsp_instruction.is_none() {
        return false;
    }

    if add_vsp_instruction.unwrap().immediate32() != 8 {
        return false;
    }

    let xchng = instruction_iter.find(|insn| match_xchng_reg(insn, new_vip));

    let new_vip_reg;
    match xchng {
        Some(xchng_insn) => {
            if !(xchng_insn.op0_register() == new_vip &&
                 xchng_insn.op1_register() == vm_context.register_allocation.vsp.into()) &&
               !(xchng_insn.op1_register() == new_vip &&
                 xchng_insn.op0_register() == vm_context.register_allocation.vsp.into())
            {
                return false;
            } else {
                new_vip_reg = vm_context.register_allocation.vsp.into();
            }
        },
        None => return false,
    }

    let store_key_reg = instruction_iter.find(|insn| match_mov_reg_source(insn, new_vip_reg));

    if store_key_reg.is_none() {
        return false;
    }

    instruction_iter.any(|insn| match_add_reg_by_amount(insn, new_vip_reg, 4))
}
/// Match a pop of a vmregister
fn vm_match_vm_reg_pop(vm_handler: &VmHandler,
                       reg_allocation: &VmRegisterAllocation)
                       -> Option<usize> {
    let mut instruction_iter = vm_handler.instructions.iter();
    instruction_iter.find(|insn| {
                        match_fetch_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                    });
    let _add_vsp_instruction =
        instruction_iter.find(|insn| match_add_vsp_get_amount(insn, reg_allocation).is_some());

    let vip_byte_fetch_instruction =
        instruction_iter.find(|insn| {
                            match_fetch_reg_any_size(insn, reg_allocation.vip.into()).is_some()
                        })?;

    let index_reg = vip_byte_fetch_instruction.op0_register().full_register();

    let store_vm_reg = instruction_iter.find(|insn| match_store_vm_reg(insn, index_reg));
    store_vm_reg.map(|insn| insn.memory_size().size())
}

/// Match a pop of a vmregister (different vmp3 version maybe idk)
fn vm_match_vm_reg_pop_v2(vm_handler: &VmHandler,
                          reg_allocation: &VmRegisterAllocation)
                          -> Option<usize> {
    let mut instruction_iter = vm_handler.instructions.iter();
    let vip_byte_fetch_instruction =
        instruction_iter.find(|insn| {
                            match_fetch_reg_any_size(insn, reg_allocation.vip.into()).is_some()
                        })?;

    let index_reg = vip_byte_fetch_instruction.op0_register().full_register();

    instruction_iter.find(|insn| {
                        match_fetch_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                    });

    let _add_vsp_instruction =
        instruction_iter.find(|insn| match_add_vsp_get_amount(insn, reg_allocation).is_some());

    let store_vm_reg = instruction_iter.find(|insn| match_store_vm_reg(insn, index_reg));
    store_vm_reg.map(|insn| insn.memory_size().size())
}
/// Match a push of a vmregister
fn vm_match_vm_reg_push(vm_handler: &VmHandler,
                        reg_allocation: &VmRegisterAllocation)
                        -> Option<usize> {
    let mut instruction_iter = vm_handler.instructions.iter();

    let vip_byte_fetch_instruction =
        instruction_iter.find(|insn| {
                            match_fetch_reg_any_size(insn, reg_allocation.vip.into()).is_some()
                        })?;

    let index_reg = vip_byte_fetch_instruction.op0_register().full_register();

    let fetch_vm_reg = instruction_iter.find(|insn| match_fetch_vm_reg(insn, index_reg));

    let _sub_vsp_instruction =
        instruction_iter.find(|insn| match_sub_vsp_get_amount(insn, reg_allocation).is_some());

    instruction_iter.find(|insn| {
                        match_store_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                    })?;

    fetch_vm_reg.map(|insn| insn.memory_size().size())
}

/// Match a n byte imm push
fn match_push_imm_n<const N: u32>(vm_handler: &VmHandler,
                                  reg_allocation: &VmRegisterAllocation)
                                  -> bool {
    let mut instruction_iter = vm_handler.instructions.iter();
    instruction_iter.find(|insn| match_sub_vsp_by_amount(insn, reg_allocation, N));
    instruction_iter.any(|insn| match_store_reg_any_size(insn, reg_allocation.vsp.into()).is_some())
}

/// Match 64 bit imm push
fn vm_match_push_imm64(vm_handler: &VmHandler,
                       reg_allocation: &VmRegisterAllocation)
                       -> bool {
    match_push_imm_n::<8>(vm_handler, reg_allocation)
}

/// Match 32 bit imm push
fn vm_match_push_imm32(vm_handler: &VmHandler,
                       reg_allocation: &VmRegisterAllocation)
                       -> bool {
    match_push_imm_n::<4>(vm_handler, reg_allocation)
}

/// Match 16 bit imm push
fn vm_match_push_imm16(vm_handler: &VmHandler,
                       reg_allocation: &VmRegisterAllocation)
                       -> bool {
    match_push_imm_n::<2>(vm_handler, reg_allocation)
}

/// Match 8 bit imm push
fn vm_match_push_imm8(vm_handler: &VmHandler,
                      reg_allocation: &VmRegisterAllocation)
                      -> bool {
    // Push of byte is sign extended
    match_push_imm_n::<2>(vm_handler, reg_allocation)
}

fn vm_match_pop_vsp_64(vm_handler: &VmHandler,
                       reg_allocation: &VmRegisterAllocation)
                       -> bool {
    let mut instruction_iter = vm_handler.instructions.iter();

    let fetch_vsp_instruction_1 =
        instruction_iter.find(|insn| {
                            match_fetch_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                        });
    if fetch_vsp_instruction_1.is_none() {
        return false;
    }

    fetch_vsp_instruction_1.unwrap().op0_register() == reg_allocation.vsp.into()
}

macro_rules! generate_binop_match {
    ($matcher_name:ident, $specific_matcher:expr) => {

        fn $matcher_name(vm_handler: &VmHandler,
                        reg_allocation: &VmRegisterAllocation)
                        -> Option<usize> {
            let mut instruction_iter = vm_handler.instructions.iter();

            let fetch_vsp_instruction_1 =
                instruction_iter.find(|insn| {
                                    match_fetch_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                                })?;
            let reg1 = fetch_vsp_instruction_1.op0_register().full_register();

            let fetch_vsp_instruction_2 =
                instruction_iter.find(|insn| {
                                    match_fetch_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                                })?;
            let reg2 = fetch_vsp_instruction_2.op0_register().full_register();

            let instruction_size = fetch_vsp_instruction_1.memory_size().size();

            $specific_matcher (&mut instruction_iter, reg1, reg2)?;

            instruction_iter.find(|insn| match_pushfq(insn))?;

            Some(instruction_size)
        }
    };
}

macro_rules! generate_binop_match_byte {
    ($matcher_name:ident, $specific_matcher:expr) => {

        fn $matcher_name(vm_handler: &VmHandler,
                        reg_allocation: &VmRegisterAllocation)
                        -> Option<usize> {
            let mut instruction_iter = vm_handler.instructions.iter();

            let fetch_vsp_instruction_1 =
                instruction_iter.find(|insn| {
                                    match_fetch_zx_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                                })?;
            let reg1 = fetch_vsp_instruction_1.op0_register().full_register();

            let fetch_vsp_instruction_2 =
                instruction_iter.find(|insn| {
                                    match_fetch_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                                })?;
            let reg2 = fetch_vsp_instruction_2.op0_register().full_register();

            let instruction_size = fetch_vsp_instruction_1.memory_size().size();

            $specific_matcher (&mut instruction_iter, reg1, reg2)?;

            instruction_iter.find(|insn| match_pushfq(insn))?;

            Some(instruction_size)
        }
    };
}

fn sub_match_add<'a, I>(instruction_iter: &mut I,
                        reg1: Register,
                        reg2: Register)
                        -> Option<&'a Instruction>
    where I: Iterator<Item = &'a Instruction>
{
    instruction_iter.find(|insn| match_add_reg_reg(insn, reg1, reg2))
}
generate_binop_match!(vm_match_add, sub_match_add);
generate_binop_match_byte!(vm_match_add_byte, sub_match_add);

fn sub_match_mul<'a, I>(instruction_iter: &mut I,
                        reg1: Register,
                        reg2: Register)
                        -> Option<&'a Instruction>
    where I: Iterator<Item = &'a Instruction>
{
    instruction_iter.find(|insn| match_mul_reg_reg(insn, reg1, reg2))
}

fn sub_match_imul<'a, I>(instruction_iter: &mut I,
                         reg1: Register,
                         reg2: Register)
                         -> Option<&'a Instruction>
    where I: Iterator<Item = &'a Instruction>
{
    instruction_iter.find(|insn| match_imul_reg_reg(insn, reg1, reg2))
}

generate_binop_match!(vm_match_mul, sub_match_mul);
generate_binop_match!(vm_match_imul, sub_match_imul);

fn sub_match_nand<'a, I>(instruction_iter: &mut I,
                         reg1: Register,
                         reg2: Register)
                         -> Option<&'a Instruction>
    where I: Iterator<Item = &'a Instruction>
{
    instruction_iter.find(|insn| match_not_reg(insn, reg1))?;
    instruction_iter.find(|insn| match_not_reg(insn, reg2))?;

    instruction_iter.find(|insn| match_or_reg_reg(insn, reg1, reg2))
}

generate_binop_match!(vm_match_nand, sub_match_nand);
generate_binop_match_byte!(vm_match_nand_byte, sub_match_nand);

fn sub_match_nor<'a, I>(instruction_iter: &mut I,
                        reg1: Register,
                        reg2: Register)
                        -> Option<&'a Instruction>
    where I: Iterator<Item = &'a Instruction>
{
    instruction_iter.find(|insn| match_not_reg(insn, reg1))?;
    instruction_iter.find(|insn| match_not_reg(insn, reg2))?;

    instruction_iter.find(|insn| match_and_reg_reg(insn, reg1, reg2))
}

generate_binop_match!(vm_match_nor, sub_match_nor);
generate_binop_match_byte!(vm_match_nor_byte, sub_match_nor);

macro_rules! generate_binop_match_single_reg {
    ($matcher_name:ident, $specific_matcher:expr) => {

        fn $matcher_name(vm_handler: &VmHandler,
                        reg_allocation: &VmRegisterAllocation)
                        -> Option<usize> {
            let mut instruction_iter = vm_handler.instructions.iter();

            let fetch_vsp_instruction_1 =
                instruction_iter.find(|insn| {
                                    match_fetch_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                                })?;
            let reg = fetch_vsp_instruction_1.op0_register();

            let _fetch_vsp_instruction_2 =
                instruction_iter.find(|insn| {
                                    match_fetch_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                                })?;

            let instruction_size = fetch_vsp_instruction_1.memory_size().size();

            $specific_matcher (&mut instruction_iter, reg)?;

            instruction_iter.find(|insn| match_pushfq(insn))?;

            Some(instruction_size)
        }
    };
}

macro_rules! generate_binop_match_byte_single_reg {
    ($matcher_name:ident, $specific_matcher:expr) => {

        fn $matcher_name(vm_handler: &VmHandler,
                        reg_allocation: &VmRegisterAllocation)
                        -> Option<usize> {
            let mut instruction_iter = vm_handler.instructions.iter();

            let fetch_vsp_instruction_1 =
                instruction_iter.find(|insn| {
                                    match_fetch_zx_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                                })?;
            let reg = fetch_vsp_instruction_1.op0_register().full_register();

            let _fetch_vsp_instruction_2 =
                instruction_iter.find(|insn| {
                                    match_fetch_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                                })?;

            let instruction_size = fetch_vsp_instruction_1.memory_size().size();

            $specific_matcher (&mut instruction_iter, reg.full_register())?;

            instruction_iter.find(|insn| match_pushfq(insn))?;

            Some(instruction_size)
        }
    };
}

fn sub_match_shr<'a, I>(instruction_iter: &mut I,
                        reg: Register)
                        -> Option<&'a Instruction>
    where I: Iterator<Item = &'a Instruction>
{
    instruction_iter.find(|insn| match_shr_reg_reg(insn, reg))
}

generate_binop_match_single_reg!(vm_match_shr, sub_match_shr);
generate_binop_match_byte_single_reg!(vm_match_shr_byte, sub_match_shr);

fn sub_match_shl<'a, I>(instruction_iter: &mut I,
                        reg: Register)
                        -> Option<&'a Instruction>
    where I: Iterator<Item = &'a Instruction>
{
    instruction_iter.find(|insn| match_shl_reg_reg(insn, reg))
}

generate_binop_match_single_reg!(vm_match_shl, sub_match_shl);
generate_binop_match_byte_single_reg!(vm_match_shl_byte, sub_match_shl);

fn sub_match_shrd<'a, I>(instruction_iter: &mut I,
                         reg: Register)
                         -> Option<&'a Instruction>
    where I: Iterator<Item = &'a Instruction>
{
    instruction_iter.find(|insn| match_shrd_reg_reg(insn, reg))
}

generate_binop_match_single_reg!(vm_match_shrd, sub_match_shrd);

fn sub_match_shld<'a, I>(instruction_iter: &mut I,
                         reg: Register)
                         -> Option<&'a Instruction>
    where I: Iterator<Item = &'a Instruction>
{
    instruction_iter.find(|insn| match_shld_reg_reg(insn, reg))
}

generate_binop_match_single_reg!(vm_match_shld, sub_match_shld);

fn vm_match_fetch(vm_handler: &VmHandler,
                  reg_allocation: &VmRegisterAllocation)
                  -> Option<usize> {
    let mut instruction_iter = vm_handler.instructions.iter();
    let fetch_vsp_instruction =
        instruction_iter.find(|insn| {
                            match_fetch_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                        })?;

    let fetch_register = fetch_vsp_instruction.op0_register();

    let mut fetch_size = 0;
    instruction_iter.find(|insn| {
                        if let Some(size) = match_fetch_reg_any_size(insn, fetch_register) {
                            fetch_size = size;
                            true
                        } else {
                            false
                        }
                    })?;

    Some(fetch_size)
}

fn vm_match_fetch_byte(vm_handler: &VmHandler,
                       reg_allocation: &VmRegisterAllocation)
                       -> Option<usize> {
    let mut instruction_iter = vm_handler.instructions.iter();
    let fetch_vsp_instruction =
        instruction_iter.find(|insn| {
                            match_fetch_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                        })?;

    let fetch_register = fetch_vsp_instruction.op0_register().full_register();

    let mut fetch_size = 0;
    instruction_iter.find(|insn| {
                        if let Some(size) = match_fetch_zx_reg_any_size(insn, fetch_register) {
                            fetch_size = size;
                            true
                        } else {
                            false
                        }
                    })?;

    Some(fetch_size)
}

fn vm_match_store(vm_handler: &VmHandler,
                  reg_allocation: &VmRegisterAllocation)
                  -> Option<usize> {
    let mut instruction_iter = vm_handler.instructions.iter();

    let fetch_vsp_instruction_1 =
        instruction_iter.find(|insn| {
                            match_fetch_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                        })?;

    let reg1 = fetch_vsp_instruction_1.op0_register().full_register();

    let fetch_vsp_instruction_2 =
        instruction_iter.find(|insn| {
                            match_fetch_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                        })?;

    let reg2 = fetch_vsp_instruction_2.op0_register().full_register();

    let mut instruction_size = 0;
    instruction_iter.find(|insn| match match_store_reg2_in_reg1(insn, reg1, reg2) {
                        Some(size) => {
                            instruction_size = size;
                            true
                        },
                        _ => false,
                    })?;
    Some(instruction_size)
}

fn vm_match_push_vsp(vm_handler: &VmHandler,
                     reg_allocation: &VmRegisterAllocation)
                     -> Option<usize> {
    let mut instruction_iter = vm_handler.instructions.iter();
    instruction_iter.find(|insn| match_mov_reg_source(insn, reg_allocation.vsp.into()))?;

    let sub_vsp_instruction =
        instruction_iter.find(|insn| match_sub_vsp_get_amount(insn, reg_allocation).is_some())?;
    let instruction_size = sub_vsp_instruction.immediate32();
    instruction_iter.find(|insn| {
                        match_store_reg_any_size(insn, reg_allocation.vsp.into()).is_some()
                    })?;

    Some(instruction_size as usize)
}

fn vm_match_vm_exit(vm_handler: &VmHandler,
                    reg_allocation: &VmRegisterAllocation)
                    -> bool {
    let instruction_iter = vm_handler.instructions.iter();

    if !instruction_iter.clone().any(match_ret) {
        return false;
    }

    if !instruction_iter.clone().any(match_popfq) {
        return false;
    }

    if !instruction_iter.clone().any(|insn| {
                                    insn.code() == Code::Mov_r64_rm64 &&
                                    insn.op0_register() == Register::RSP &&
                                    insn.op1_register() == reg_allocation.vsp.into()
                                })
    {
        return false;
    }

    if instruction_iter.filter(|insn| insn.code() == Code::Pop_r64)
                       .count() !=
       15
    {
        return false;
    }

    true
}

fn vm_match_push_cr0(vm_handler: &VmHandler) -> bool {
    let first_instruction = vm_handler.instructions[0];
    (first_instruction.code() == Code::Mov_r64_cr) &&
    first_instruction.op1_register() == Register::CR0
}

fn vm_match_nop(vm_handler: &VmHandler) -> bool {
    let first_instruction = vm_handler.instructions[0];
    first_instruction.code() == Code::Lea_r64_m
}
