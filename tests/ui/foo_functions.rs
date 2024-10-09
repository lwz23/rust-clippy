#![allow(unused)]
#![warn(clippy::foo_functions)]


fn main() {
    let value: i32 = 42;
    
        let a=1;
        let b=2;
        
        
        let a=1;
        let b=2;
        unsafe{
            for i in 0..10 {
                let ptr: *const i32 = &value;
                let double_value = value * 2;
                let dereferenced_value = *ptr; //only one unsafe op here
            }
            
        }
        
    
        
}
    






