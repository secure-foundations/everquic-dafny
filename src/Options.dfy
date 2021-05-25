module Options {
  datatype Option<V> = None | Some(value:V)

  datatype Err<V> = Fail(err:string) | Ok(value:V)
}

