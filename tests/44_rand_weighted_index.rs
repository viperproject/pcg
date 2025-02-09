#[derive(Debug)]
pub enum Error {
    InvalidInput,
    InvalidWeight,
    InsufficientNonZero,
}

pub struct WeightedIndex<X> {
    cumulative_weights: Vec<X>,
    total_weight: X,
    weight_distribution: X,
}

impl<X> WeightedIndex<X>
where
    X: for<'a> core::ops::AddAssign<&'a X>
        + for<'a> core::ops::SubAssign<&'a X>
        + Clone
        + Default
        + PartialOrd,
{
    pub fn update_weights(&mut self, new_weights: &[(usize, &X)]) -> Result<(), Error> {
        if new_weights.is_empty() {
            return Ok(());
        }

        let zero = <X as Default>::default();

        let mut total_weight = self.total_weight.clone();

        // Check for errors first, so we don't modify `self` in case something
        // goes wrong.
        let mut prev_i = None;
        for &(i, w) in new_weights {
            if let Some(old_i) = prev_i {
                if old_i >= i {
                    return Err(Error::InvalidInput);
                }
            }
            if !(*w >= zero) {
                return Err(Error::InvalidWeight);
            }
            if i > self.cumulative_weights.len() {
                return Err(Error::InvalidInput);
            }

            let mut old_w = if i < self.cumulative_weights.len() {
                self.cumulative_weights[i].clone()
            } else {
                total_weight.clone()
            };
            if i > 0 {
                old_w -= &self.cumulative_weights[i - 1];
            }

            total_weight -= &old_w;
            total_weight += w;
            prev_i = Some(i);
        }
        if total_weight <= zero {
            return Err(Error::InsufficientNonZero);
        }

        // Update the weights. Because we checked all the preconditions in the
        // previous loop, this should never panic.
        let mut iter = new_weights.iter();

        let mut prev_weight = zero.clone();
        let mut next_new_weight = iter.next();
        let &(first_new_index, _) = next_new_weight.unwrap();
        let mut cumulative_weight = if first_new_index > 0 {
            self.cumulative_weights[first_new_index - 1].clone()
        } else {
            zero.clone()
        };
        for i in first_new_index..self.cumulative_weights.len() {
            match next_new_weight {
                Some(&(j, w)) if i == j => {
                    cumulative_weight += w;
                    next_new_weight = iter.next();
                }
                _ => {
                    let mut tmp = self.cumulative_weights[i].clone();
                    tmp -= &prev_weight; // We know this is positive.
                    cumulative_weight += &tmp;
                }
            }
            prev_weight = cumulative_weight.clone();
            core::mem::swap(&mut prev_weight, &mut self.cumulative_weights[i]);
        }

        self.total_weight = total_weight.clone();
        self.weight_distribution = total_weight;

        Ok(())
    }
}

fn main() {
    // Example usage
    let mut wi: WeightedIndex<f64> = WeightedIndex {
        cumulative_weights: vec![1.0, 3.0, 6.0],
        total_weight: 6.0,
        weight_distribution: 6.0,
    };

    let new_weights = vec![(1, &2.0)];
    let _ = wi.update_weights(&new_weights);
}
