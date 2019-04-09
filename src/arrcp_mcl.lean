import mcl
open mcl

namespace arrcp_mcl

def sig : signature
| _ := type.int

def arrcp₁ : mclp sig := mclp.intro (λ m, 10) (mclk.global_assign "b" (expression.const_int 7 (by refl)))

def arrcp₂ : mclp sig := mclp.intro (λ m, 10) (mclk.global_assign "c" (expression.const_int 9 (by refl)))

example : mclp_rel (λ m₁ m₂, sorry) arrcp₁ arrcp₂ (λ m₁ m₂, sorry) := begin
    
end

end arrcp_mcl