use std::time::Instant;
fn run_expensive_calculation(){}
fn main() {
  let start = Instant::now();
  run_expensive_calculation();
  let elapsed = start.elapsed();
  println!("Elapsed: {}s", elapsed.as_secs());
}
