use std::io;

pub fn copy_from_to<R: io::Read, W: io::Write>(mut r: R, mut w: W) -> io::Result<usize> {
  let mut buffer: [u8; 65536] = [0; 65536];
  let mut out_size: usize = 0;
  loop {
    match r.read(&mut buffer[..]) {
      Err(e) => {
        return Err(e);
      }
      Ok(size) => {
        w.write_all(&buffer[..size]);
      }
    }
  }
  Ok(out_size)
}

fn main(){

}
