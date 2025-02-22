use std::cmp;
use std::mem;

#[derive(Clone)]
pub struct InflateState {
    dict_avail: usize,
    dict_ofs: usize,
    dict: Vec<u8>,
}

const TINFL_LZ_DICT_SIZE: usize = 32_768;

fn push_dict_out(state: &mut InflateState, next_out: &mut &mut [u8]) -> usize {
    let n = cmp::min(state.dict_avail, next_out.len());
    (next_out[..n]).copy_from_slice(&state.dict[state.dict_ofs..state.dict_ofs + n]);
    *next_out = &mut mem::take(next_out)[n..];
    state.dict_avail -= n;
    state.dict_ofs = (state.dict_ofs + (n)) & (TINFL_LZ_DICT_SIZE - 1);
    n
}

fn main(){}
