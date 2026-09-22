# Clos2 - Closure Conversion in MimIR
The Target of this project is to add closure conversion to the research compiler [MimIR](https://github.com/mimir/mimir).

## Closure Conversion
TODO describe what CC is.

## Notes
because I'm currently only interested in the absract typed closure conversion I currently do not have to think about where the environment will be placed (stack or heap)

I want to complie with the following requirements
1. A typed closure abstraction **must hide the type of the environment**
2. A typed closure abstraction **must enforce the calling convention** :\\
   the code pointer is called with **its packaged environment**.
   - for this we have to give a prove that the code pointer is only beeing called with and only with the environment which was created for it.\\
     this can be enforced by the type-system by using `singleton` types.
3. Procedures are directly callable through their code pointer


## Installation
Because this is a plugin for `MimIR` you will have to clone [it's repository](https://github.com/mimir/mimir) and get it to work.

Then you can add this plugin by cloning this repository into `extra/`

MimIR will take care of the rest and will include this plugin in the next build.

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

classical example: of impredicativity bugs I had to work on:
```
note: expected [*, [*, *, Cn [*, [I32, [*, *, Cn [*, I32]]]]]], got [*, [*, *, Cn [*, [I32, [*, *, Cn [*, I32]]]]]]
```


### example with the existential hiding of the environment.
Note that this will most likely fail for dependently typed functions and polymorphic functions, because mim has a predicative universe hierarchy.

```mim
plugin core;
plugin mem;
import compile;
import pipeline;
plugin compile;
plugin clos2;

extern fun make_adder (n_5306: I32): Cn [I32, Cn I32] =
    con f_5301 (x_5304: I32, return_5312: Cn I32) as _5303 =
        let _5311 = core.wrap.add 0 @ i32 (x_5304, n_5306);
        return_5312 _5311;

    return f_5301;

extern con main (m_5289: mem.M 0, argc_5286: I32, _: mem.Ptr (mem.Ptr (I8, 0), 0), return_5293: Cn [mem.M 0, I32]) as _5285 =
    con _5281 (add2_5296: Cn [I32, Cn I32]) =
        con _5287 (c_5290: I32) =
            return_5293 (m_5289, c_5290);

        add2_5296 (argc_5286, _5287);

    make_adder (2I32, _5281);
```
has the following output
```mim
plugin core;
plugin mem;
import compile;
import pipeline;
plugin compile;
plugin clos2;

extern con procedure_make_adder (_5310: «()», (n_5313: I32, (N_5353: *, _5354: _5311#tt#0₃, _5357: Cn [_5311#tt#0₃, [N_5295: *, N_5295, Cn [N_5295, [I32, [N_5298: *, N_5298, Cn [N_5298, I32]]]]]]) as return_5312) as _5311) as _5309 =
    con procedure_f_5326 (_5328: «_5311#ff», (x_5335: I32, (N_5338: *, _5339: _5329#tt#0₃, _5342: Cn [_5329#tt#0₃, I32]) as return_5330) as _5329) as _5327 =
        let _5337 = core.wrap.add 0 @ i32 (_5329#ff, _5311#ff);
        _5329#tt#2₃ (_5329#tt#1₃, _5337);

    _5311#tt#2₃ (_5311#tt#1₃, («_5311#ff», ‹_5311#ff›, procedure_f_5326));

extern con procedure_main (_5285: «()», (m_5397: mem.M 0, argc_5401: I32, _: mem.Ptr (mem.Ptr (I8, 0), 0), (N_5427: *, _5428: _5286#3₄#0₃, _5431: Cn [_5286#3₄#0₃, [mem.M 0, I32]]) as return_5399) as _5286) as _5284 =
    con procedure__5410 (_5412: «(_5286#0₄, _5286#3₄, _5286#1₄)», (N_5443: *, _5444: _5413#0₃, _5447: Cn [_5413#0₃, [I32, [N_5384: *, N_5384, Cn [N_5384, I32]]]]) as _5413) as _5411 =
        con procedure__5422 (_5424: «(_5286#3₄, _5286#0₄)», _5425: I32) as _5423 =
            _5286#3₄#2₃ (_5286#3₄#1₃, (_5286#0₄, _5425));

        _5413#2₃ (_5413#1₃, (_5286#1₄, («(_5286#3₄, _5286#0₄)», ‹(_5286#3₄, _5286#0₄)›, procedure__5422)));

    procedure_make_adder (‹()›, (2I32, («(_5286#0₄, _5286#3₄, _5286#1₄)», ‹(_5286#0₄, _5286#3₄, _5286#1₄)›, procedure__5410)));
```
