use std::error::Error;

use haybale::{
    config::NullPointerChecking, get_possible_return_values_of_func, Config, Project, ReturnValue,
};

pub fn get_possible_solutions(function_name: &str) -> Result<Vec<u64>, Box<dyn Error>> {
    let project = Project::from_bc_path("devirt.bc")?;

    // println!("Pointer size = {}", project.pointer_size_bits());

    let mut config: Config<haybale::backend::DefaultBackend> = Default::default();
    config.null_pointer_checking = NullPointerChecking::None;

    config.function_hooks.add("llvm.ctpop.i8", &|state, call| {
                             let _arguments = call.get_arguments();
                             Ok(ReturnValue::Return(state.new_bv_with_name("ctpop".into(),
                                                                           8)
                                                         .unwrap()))
                         });
    config.function_hooks.add("llvm.fshl.i64", &|state, call| {
                             let _arguments = call.get_arguments();
                             Ok(ReturnValue::Return(state.new_bv_with_name("fshl".into(),
                                                                           64)
                                                         .unwrap()))
                         });
    config.function_hooks.add("llvm.fshl.i32", &|state, call| {
                             let _arguments = call.get_arguments();
                             Ok(ReturnValue::Return(state.new_bv_with_name("fshl".into(),
                                                                           32)
                                                         .unwrap()))
                         });
    config.function_hooks
          .add_default_hook(&|_, _| Ok(ReturnValue::ReturnVoid));

    let possible_solutions =
        get_possible_return_values_of_func(function_name, &project, config, None, None, 10);

    let mut solutions_return = Vec::new();
    match possible_solutions {
        haybale::solver_utils::PossibleSolutions::Exactly(solutions) => {
            for solution in solutions {
                match solution {
                    ReturnValue::Return(value) => {
                        // println!("Branch target -> {:x}", value);
                        solutions_return.push(value);
                    },
                    ReturnValue::ReturnVoid => panic!(),
                    ReturnValue::Throw(_) => panic!(),
                    ReturnValue::Abort => panic!(),
                };
            }
        },
        haybale::solver_utils::PossibleSolutions::AtLeast(_) => {
            panic!("More than 10 options for next vip!")
        },
    }
    Ok(solutions_return)
}
