use std::collections::{HashMap, HashSet, VecDeque};
use std::error::Error;

use pelite::pe64::PeFile;
use pelite::FileMap;

use clap::Parser;
use std::io::Write;

use petgraph::dot::Config;
use petgraph::graphmap::GraphMap;
use petgraph::visit::NodeRef;

mod llvm_ir_gen;
mod match_assembly;
mod symbolic;
mod transforms;
mod util;
mod vm_handler;
mod vm_matchers;

use vm_handler::VmContext;

use crate::llvm_ir_gen::VmLifter;
use crate::vm_matchers::HandlerVmInstruction;

fn parse_hex_vm_call(input_str: &str) -> Result<u64, std::num::ParseIntError> {
    let str_trimmed = input_str.trim_start_matches("0x");
    u64::from_str_radix(str_trimmed, 16)
}

#[derive(Parser, Debug)]
struct CommandLineArgs {
    /// Input file
    pub input_file:      String,
    /// Vm call address
    /// Address of the push instruction in
    /// push <const>
    /// call vm_entry
    #[clap(short, long, parse(try_from_str = parse_hex_vm_call))]
    pub vm_call_address: u64,
    /// Max blocks for slicing
    #[clap(long)]
    pub max_blocks: Option<u64>,
}

fn main() -> Result<(), Box<dyn Error>> {
    let command_line_args = CommandLineArgs::parse();
    let input_file = &command_line_args.input_file;

    let map = FileMap::open(input_file)?;
    let pe_file = PeFile::from_bytes(&map)?;
    let pe_bytes = std::fs::read(input_file)?;

    let mut control_flow_graph = GraphMap::<u64, (), petgraph::Directed>::new();

    let vm_lifter = VmLifter::new();

    let mut vm_context =
        VmContext::new_from_vm_entry(&pe_file, &pe_bytes, command_line_args.vm_call_address);

    println!("{:x?}", vm_context);

    let handlers = vm_context.disassemble_context(&pe_file, &pe_bytes);
    let last_handler = *handlers.last().unwrap();

    vm_lifter.lift_helper_stub(&vm_context, &handlers);

    let mut explored = HashMap::new();
    let mut worklist = VecDeque::new();
    let mut reprove_list = VecDeque::new();

    let root_vip = vm_context.initial_vip;
    control_flow_graph.add_node(root_vip);

    if last_handler.1 != HandlerVmInstruction::VmExit {
        let next_vips = vm_lifter.slice_vip(&control_flow_graph, vm_context.initial_vip, root_vip, command_line_args.max_blocks)?;

        for target_vip in next_vips {
            worklist.push_back((vm_context.clone(), last_handler, target_vip));
            explored.insert(root_vip, (vm_context.clone(), last_handler));
        }
    }

    loop {
        println!("Worklist {:#x?}",
                 worklist.iter()
                         .map(|(_, _, target)| target)
                         .collect::<Vec<_>>());
        println!("Explored {:#x?}", explored.keys());
        println!("Reprove {:#x?}",
                 reprove_list.iter()
                             .map(|(_, _, target)| target)
                             .collect::<Vec<_>>());

        if worklist.is_empty() {
            if reprove_list.is_empty() {
                break;
            } else {
                while !reprove_list.is_empty() {
                    let reprove = reprove_list.pop_front().unwrap();
                    worklist.push_back(reprove);
                }
            }
        }

        // Should never panic because we explicitly check that the list is not empty
        // first
        let (vm_context, last_handler, target_vip) = worklist.pop_front().unwrap();
        if explored.contains_key(&target_vip) {
            if control_flow_graph.contains_edge(vm_context.initial_vip, target_vip) {
                continue;
            }

            let outgoing_edges =
                control_flow_graph.edges_directed(target_vip, petgraph::EdgeDirection::Outgoing);
            for (_, target, _) in outgoing_edges {
                let (vm_context, last_handler) = explored.get(&target).unwrap();
                reprove_list.push_back((vm_context.clone(), *last_handler, target));
                explored.remove(&target);
            }
        }

        explored.insert(target_vip, (vm_context.clone(), last_handler));
        control_flow_graph.add_edge(vm_context.initial_vip, target_vip, ());

        if last_handler.1 == HandlerVmInstruction::VmExit {
            continue;
        }

        let mut new_vm_context =
            vm_context.new_from_jump_handler(&last_handler, target_vip, &pe_file, &pe_bytes);

        let new_handlers = new_vm_context.disassemble_context(&pe_file, &pe_bytes);
        // If this panics shit is fucked anyways
        let last_handler = *new_handlers.last().unwrap();

        vm_lifter.lift_helper_stub(&new_vm_context, &new_handlers);

        // Skip slicing since exit
        if last_handler.1 == HandlerVmInstruction::VmExit {
            continue;
        }

        if last_handler.1 == HandlerVmInstruction::Nop {
            let next_vip = new_vm_context.vip_value;

            worklist.push_back((new_vm_context.clone(), last_handler, next_vip));
            continue;
        }

        let next_vips =
            vm_lifter.slice_vip(&control_flow_graph, new_vm_context.initial_vip, root_vip, command_line_args.max_blocks)?;
        for next_vip in next_vips {
            worklist.push_back((new_vm_context.clone(), last_handler, next_vip));
            println!("Next vip -> {:#x}", next_vip);
        }
    }

    let mut dot_file = std::fs::File::create("cfg.dot")?;
    writeln!(dot_file,
             "{:?}",
             petgraph::dot::Dot::with_attr_getters(&control_flow_graph,
                                                   &[Config::EdgeNoLabel, Config::NodeNoLabel],
                                                   &|_, _| { "".to_owned() },
                                                   &|_, node_ref| {
                                                       format!("label = \"{:#x}\"",
                                                               node_ref.weight())
                                                   }))?;

    vm_lifter.create_helper_function(&control_flow_graph, root_vip);

    vm_lifter.optimize_module_no_global_delete();
    vm_lifter.fix_arg_names(&format!("helperfunction_{:x}", root_vip));
    vm_lifter.print_function(&format!("helperfunction_{:x}", root_vip));
    vm_lifter.output_module();
    Ok(())
}
