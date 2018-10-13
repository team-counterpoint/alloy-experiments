/*
 * Copyright (c) 2017, Amirhossein Vakili, Sabria Farheen, Nancy A. Day, Ali Abbassi
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without 
 * modification, are permitted provided that the following conditions 
 * are met:
 *
 *    1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    2. Redistributions in binary form must reproduce the above copyright 
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT 
 * HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

module ctlfc[S]


//********************KRIPKE STRUCTURE DEF*************************//

private one sig TS{
    S0: some S,
    sigma: S -> S,
    FC: set S
}


//********************MODEL SET UP FUNCTIONS*************************//
// set by users in their model files

fun initialState: S {TS.S0}

fun nextState: S -> S{TS.sigma}

fun fc: S {TS.FC}


//********************HELPER FUNCTIONS*************************//

private fun domainRes[R: S -> S, X: S]: S -> S{X <: R}
private fun id[X:S]: S->S{domainRes[iden,X]}


//********************FAIR STATES DEF*************************//
// Fair is EcG true
private fun Fair: S{
    let R= TS.sigma|
        *R.((^R & id[S]).S & TS.FC)
}
 

//********************LOGICAL OPERATORS*************************//

fun not_[phi: S]: S {S - phi}
fun and_[phi, si: S]: S {phi & si}
fun or_[phi, si: S]: S {phi + si}
fun imp_[phi, si: S]: S {not_[phi] + si}


//********************TEMPORAL OPERATORS*************************//

fun ex[phi: S]: S {TS.sigma.(phi & Fair)}

fun ax[phi:S]:S {not_[ex[not_[phi]]]}

fun ef[phi: S]: S {(*(TS.sigma)).(phi & Fair)}

fun eg[phi:S]:S { 
    let R= domainRes[TS.sigma,phi]|
        *R.((^R & id[S]).S & TS.FC)
}

fun af[phi: S]: S {not_[eg[not_[phi]]]}

fun ag[phi: S]: S {not_[ef[not_[phi]]]}

fun eu[phi, si: S]: S {(*(domainRes[TS.sigma, phi])).(si & Fair)}

fun au[phi, si: S]:S {
    not_[or_[eg[not_[si]],
         		eu[not_[si],
                not_[or_[phi, si]]]]]
}


//********************MODEL CHECKING CONSTRAINT*************************//
// called by users for mc in their model file
pred ctlfc_mc[phi: S]{TS.S0 in phi}
