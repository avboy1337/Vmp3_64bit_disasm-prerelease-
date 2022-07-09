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
    pub vm_call_addresses: Vec<u64>,
    /// Max blocks for slicing
    #[clap(long)]
    pub max_blocks:      Option<u64>,
}

fn main() -> Result<(), Box<dyn Error>> {
    let command_line_args = CommandLineArgs::parse();
    let input_file = &command_line_args.input_file;

    let map = FileMap::open(input_file)?;
    let pe_file = PeFile::from_bytes(&map)?;
    let pe_bytes = std::fs::read(input_file)?;

    // Create the `VmLifter`
    let vm_lifter = VmLifter::new();

    // Lift all the functions specified
    for address in command_line_args.vm_call_addresses.iter().cloned() {
        explore_cfg_and_lift_function(&pe_file, &pe_bytes, address, &vm_lifter, command_line_args.max_blocks)?;
    }

    // We do not want to delete globals in this case as it messes up recompilation
    vm_lifter.optimize_module_no_global_delete();


    for address in command_line_args.vm_call_addresses.iter().cloned() {
        // Fix the argument names since a stripping pass is included
        vm_lifter.fix_arg_names(&format!("helperfunction_{:x}", address));

        // Print the function to stderr
        vm_lifter.print_function(&format!("helperfunction_{:x}", address));
    }


    // Output the module to an ir file devirt.ll
    vm_lifter.output_module();

    Ok(())
}

fn explore_cfg_and_lift_function(pe_file: &PeFile, pe_bytes: &[u8], vm_call_address: u64, vm_lifter: &VmLifter, max_blocks: Option<u64>) -> Result<(), Box<dyn Error>> {

    // Cfg exploration
    let mut explored = HashMap::new();
    let mut worklist = VecDeque::new();
    let mut reprove_list = VecDeque::new();

    let mut control_flow_graph = GraphMap::<u64, (), petgraph::Directed>::new();


    // `VmContext` for the first block
    let mut vm_context =
        VmContext::new_from_vm_entry(pe_file, pe_bytes, vm_call_address);

    let root_vip = vm_context.initial_vip;

    // Disassemble the handlers
    let handlers = vm_context.disassemble_context(pe_file, pe_bytes);
    // Get the last handler
    let last_handler = *handlers.last().unwrap();

    // Lift this first block into a stub
    vm_lifter.lift_helper_stub(&vm_context, &handlers);

    // Add the first block to the cfg
    control_flow_graph.add_node(root_vip);

    // Handle special case of the first block ending in nop
    if last_handler.1 == HandlerVmInstruction::Nop {

        worklist.push_back((vm_context.clone(), last_handler, vm_context.vip_value));
        explored.insert(root_vip, (vm_context, last_handler));
    
    } else if last_handler.1 != HandlerVmInstruction::VmExit {
        let next_vips = vm_lifter.slice_vip(&control_flow_graph,
                                            vm_context.initial_vip,
                                            root_vip,
                                            max_blocks)?;

        for target_vip in next_vips {
            worklist.push_back((vm_context.clone(), last_handler, target_vip));
            explored.insert(root_vip, (vm_context.clone(), last_handler));
        }
    }

    loop {
        // Print the current lists

        println!("Worklist {:#x?}",
                 worklist.iter()
                         .map(|(_, _, target)| target)
                         .collect::<Vec<_>>());
        println!("Explored {:#x?}", explored.keys());
        println!("Reprove {:#x?}",
                 reprove_list.iter()
                             .map(|(_, _, target)| target)
                             .collect::<Vec<_>>());

        // If the worklist is empty extend it with the reprove list, if that is empty
        // we're done
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
        // Get an item from the worklist
        // Contains the vm_context of the handler that branched to current_block_vip
        // And the last handler that branched to current_block_vip
        // This iteration we start disassembling from current_block_vip
        let (prev_block_vm_context, last_prev_block_handler, current_block_vip) =
            worklist.pop_front().unwrap();

        // Check if already visited
        if explored.contains_key(&current_block_vip) {
            // Ok nothing to do because we already new about this edge
            if control_flow_graph.contains_edge(prev_block_vm_context.initial_vip,
                                                current_block_vip)
            {
                continue;
            }
            // Ok stuff to do because we did not know about this edge yet but it goes to a
            // block we did know about
            //
            //
            // Get the edges of the cfg that start from current_block_vip
            let outgoing_edges =
                control_flow_graph.edges_directed(current_block_vip,
                                                  petgraph::EdgeDirection::Outgoing);

            // target contains the destination of the edge from current_block_vip
            for (_, target, _) in outgoing_edges {
                // Ok get all the blocks the current_block_vip block could branch to
                let target_block = explored.get(&target);
                
                match target_block {
                    Some(entry) => {let (vm_context, last_handler) = entry;
                    // Add them to the reprove list
                     reprove_list.push_back((vm_context.clone(), *last_handler, target));
                // We remove them from explored
                   explored.remove(&target);},
                None => {
                        // Still in the worklist and not yet explored nothing to do
                    },
            }
            }
        }

        // Add the edge from the previous block to the current block
        println!("ADDING EDGE {:#x} -> {:#x}",
                 prev_block_vm_context.initial_vip, current_block_vip);
        control_flow_graph.add_edge(prev_block_vm_context.initial_vip, current_block_vip, ());

        // Ok we now explore this block so add it to explored
        explored.insert(current_block_vip,
                        (prev_block_vm_context.clone(), last_prev_block_handler));

        // This condition is here for the case of single block stubs
        if last_prev_block_handler.1 == HandlerVmInstruction::VmExit {
            continue;
        }

        // Debug printing
        println!("Previous vm_context start_vip -> {:#x}",
                 prev_block_vm_context.initial_vip);
        println!("Getting vm_context at current_block_vip -> {:#x}",
                 current_block_vip);

        let mut current_block_vm_context;

        // If the last block ended in a nop
        if last_prev_block_handler.1 == HandlerVmInstruction::Nop {
            current_block_vm_context = prev_block_vm_context;
            current_block_vm_context.initial_vip = current_block_vm_context.vip_value;
        } else {
            current_block_vm_context =
                prev_block_vm_context.new_from_jump_handler(&last_prev_block_handler,
                                                            current_block_vip,
                                                            pe_file,
                                                            pe_bytes);
        }

        // Get the new handler of the current_block_vip block
        let current_block_handlers =
            current_block_vm_context.disassemble_context(pe_file, pe_bytes);

        // If this panics shit is fucked anyways
        let last_current_block_handler = *current_block_handlers.last().unwrap();

        // Lift the new handlers into a helper stub
        vm_lifter.lift_helper_stub(&current_block_vm_context, &current_block_handlers);

        // Skip slicing since exit
        if last_current_block_handler.1 == HandlerVmInstruction::VmExit {
            continue;
        }

        // Skip slicing because NOP
        if last_current_block_handler.1 == HandlerVmInstruction::Nop {
            let target_vip = current_block_vm_context.vip_value;
            println!("NOP target_vip -> {:#x}", target_vip);

            worklist.push_back((current_block_vm_context, last_current_block_handler, target_vip));
            continue;
        }

        let next_vips = vm_lifter.slice_vip(&control_flow_graph,
                                            current_block_vm_context.initial_vip,
                                            root_vip,
                                            max_blocks)?;
        for next_vip in next_vips {
            worklist.push_back((current_block_vm_context.clone(),
                                last_current_block_handler,
                                next_vip));
            println!("Next vip -> {:#x}", next_vip);
        }
    }

    // // Write out the control flow graph to a dot file
    // let mut dot_file = std::fs::File::create("cfg.dot")?;
    // writeln!(dot_file,
    //          "{:?}",
    //          petgraph::dot::Dot::with_attr_getters(&control_flow_graph,
    //                                                &[Config::EdgeNoLabel, Config::NodeNoLabel],
    //                                                &|_, _| { "".to_owned() },
    //                                                &|_, node_ref| {
    //                                                    format!("label = \"{:#x}\"",
    //                                                            node_ref.weight())
    //                                                }))?;

    // Create the final lifted function
    let helper_function = vm_lifter.create_helper_function(&control_flow_graph, root_vip, vm_call_address);
    Ok(())
}
