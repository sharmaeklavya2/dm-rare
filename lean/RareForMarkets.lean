module

import AxiomCheck
import RareForMarkets.Defs.Market
import RareForMarkets.Defs.Misc
import RareForMarkets.Defs.Rare
import RareForMarkets.Exist.Main
import RareForMarkets.Dynamics.Main
import RareForMarkets.Prelims
import RareForMarkets.NashEq.NonRivalUncommon
import RareForMarkets.NashEq.ReductionToRival

section
set_option linter.hashCommand false

-- Existence of RARE
#check_axioms rare_exists_continuous
#check_axioms rare_exists_continuous_corr
#check_axioms unique_nr_demand
#check_axioms nonrival_rare_exists
#check_axioms unique_rival_demand
#check_axioms rival_rare_exists

-- Dynamics for RARE
#check_axioms dynamics_sellout
#check_axioms dynamics_convergence

-- Non-existence of Nash equilibrium
#check_axioms nasheq_uncommon
#check_axioms rivalize_allocRule_mem
#check_axioms rivalize_isNashEq_iff

end
