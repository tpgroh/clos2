# Clos2 - Closure Conversion in MimIR
The Target of this project is to add closure conversion to the research compiler [MimIR](https://github.com/mimir/mimir).

## Closure Conversion
TODO describe what Closure Conversion is.

## Installation
Because this is a plugin for `MimIR` you will have to clone [it's repository](https://github.com/mimir/mimir) and get it to work.

Then you can add this plugin by cloning this repository into `extra/`

MimIR will take care of the rest and will include this plugin in the next build.

## Why not for Calculus of Constructions
The current state of research seems to be that closure conversion for CC is only possible as an abstract closure conversion,
thus requiring a different target language.

To my knowledge there is currently no way to do that in MimIR without modifying the mim language, which would be counterproductive in my opinion.

Theoretically there could be a way to get it to work:
1. Closure conversion from CC to CC-CC or something alike — there are already holes in that transformation for MimIR
2. CC-CC into something like ACC
3. ACC to FCC (modified to work with type-passing polymorphism, and possibly dependent types if no way is found to remove them with another translation pass before)
4. FCC optimization
5. FCC to mim

To my knowladge there is currently no way to do that in MimIR without modifying the mim language which would be counter productive in my opinion.

Theoreticly there could be a way to get it to work.
1. closure conversion from CC to CC-CC or something alike, there are already holes in that transformation for MimIR
2. CC-CC into something like ACC
3. ACC to FCC (modifyed to work with type passing polymorphism + maybe dependent types if no way is found to remove dependent types with another translation before)
4 FCC Optimization
5 FCC to mim

# Current Example
### reached clos2 clos_conv phase
```mim
plugin core;
plugin mem;
import compile;
import pipeline;
plugin compile;
plugin clos2;

extern fun main ((m_3963: mem.M 0, argc_3964: I32, _: mem.Ptr (mem.Ptr (I8, 0), 0)) as _3962): [mem.M 0, I32] =
    con _3960 (add2_3965: I32 → I32)@(ff) =
        let _3966: I32 = add2_3965 _3962#1₃;
        return_3968 (_3962#0₃, _3966);
    
    make_adder_3972 (2I32, _3960);

fun make_adder_3972 (n_3977: I32): I32 → I32 =
    lam adder_3973 (x_3975: I32): I32 =
        core.wrap.add 0 i32 (x_3975, n_3977);
    
    return_3983 adder_3973;
```

### result of clos_conv phase
```mim
plugin core;
plugin mem;
import compile;
import pipeline;
plugin compile;
plugin clos2;

// NOTE: main was not transformed because of its name.

extern fun main ((environment_m_4979: mem.M 0, environment_argc_4978: I32, _: mem.Ptr (mem.Ptr (I8, 0), 0)) as _4977): [mem.M 0, I32] =
    procedure_make_adder_5002 () (2I32, procedure__4988 (_4977#1₃, _4977#0₃, environment_return_4980));

con procedure__4988 (env_ext_0_argc_4990: I32, env_ext_1_m_4991: mem.M 0, env_ext_2_return_4992: Cn [mem.M 0, I32]) as env_4989 (arg_4994: I32 → I32)@(ff) =
    let _4995: I32 = arg_4994 env_ext_0_argc_4990;
    env_ext_2_return_4992 (env_ext_1_m_4991, _4995);

fun procedure_make_adder_5002 () (environment_n_5005: I32): I32 → I32 =
    return_5020 (procedure_adder_5008 environment_n_5005);

fun _5003 (environment_n_5005: I32): I32 → I32 =
    return_5020 (procedure_adder_5008 environment_n_5005);

lam procedure_adder_5008 (env_n_5009: I32) (arg_5011: I32): I32 =
    core.wrap.add 0 i32 (env_n_5009, arg_5011);
```
