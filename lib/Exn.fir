prim throw[a, r](exn: [..r]): {..r} a

prim try[a, exn, r](cb: Fn(): {..exn} a): {..r} Result[[..exn], a]

untry[a, errs](res: Result[[..errs], a]): {..errs} a
    match res:
        Result.Ok(a): a
        Result.Err(err): throw(err)
