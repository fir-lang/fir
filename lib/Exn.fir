prim throw(exn: [..r]): {..r} a

prim try(cb: Fn(): {..exn} a): {..r} Result[[..exn], a]

untry(res: Result[[..errs], a]): {..errs} a
    match res:
        Result.Ok(a): a
        Result.Err(err): throw(err)
