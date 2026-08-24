import WPPCompactSourceSyntax
import WPPCompactSyntaxFVExplicit
import CompactSyntaxFV
import CoreFVSimp
import NominalSubstitutionLemmas
import NominalDefinitionRefl
import NominalDfEu
import NominalAlphaRepairedDfNfc001
import NominalAlphaRepairedBase001003V
import NominalAlphaRepairedBase001004Csb
import NominalAlphaRepairedBase001005Nin
import NominalAlphaRepairedBase001006If
import NominalAlphaRepairedBase001007Pw
import NominalAlphaRepairedBase001008Sn
import NominalAlphaRepairedBase001009Uni
import NominalAlphaRepairedBase001010Int
import NominalAlphaRepairedBase001011Iun
import NominalAlphaRepairedBase001012Leaf1c
import NominalAlphaRepairedBase001013Xpk
import NominalAlphaRepairedBase001014Cnvk
import NominalAlphaRepairedBase001015Ins2k
import NominalAlphaRepairedBase001016Ins3k
import NominalAlphaRepairedBase001017Imak
import NominalAlphaRepairedBase001018P6
import NominalAlphaRepairedBase001019Sik
import NominalAlphaRepairedBase001020Ssetk
import NominalAlphaRepairedBase001021Idk
import NominalAlphaRepairedBase001022Iota
import NominalAlphaRepairedBase001023Addc
import NominalAlphaRepairedBase001024Nnc
import NominalAlphaRepairedBase001025Lefin
import NominalAlphaRepairedBase001026Ltfin
import NominalAlphaRepairedBase001027Ncfin
import NominalAlphaRepairedBase001028Tfin
import NominalAlphaRepairedBase001029Evenfin
import NominalAlphaRepairedBase001030Oddfin
import NominalAlphaRepairedBase001031Sfin
import NominalAlphaRepairedBase001032Spfin
import NominalAlphaRepairedBase001033Phi
import NominalAlphaRepairedBase001034OpReflected001
import NominalAlphaRepairedBase001035Proj1Reflected001
import NominalAlphaRepairedBase001036Proj2Reflected001
import NominalAlphaRepairedBase001037OpabOpaqueHoisted004
import NominalAlphaRepairedBase001038Leaf1stReflected001
import NominalAlphaRepairedBase001039SwapReflected001
import NominalAlphaRepairedBase001040SsetReflected001
import NominalAlphaRepairedBase001041CoReflected001
import NominalAlphaRepairedBase001042ImaReflected001
import NominalAlphaRepairedBase001043SiReflected001
import NominalAlphaRepairedBase001044IdReflected001
import NominalAlphaRepairedBase001045XpReflected001
import NominalAlphaRepairedBase001046CnvReflected001
import NominalAlphaRepairedBase001047FvReflected001
import NominalAlphaRepairedBase001048Leaf2ndReflected001
import NominalAlphaRepairedBase001049OprabReflected001
import NominalAlphaPrefix050WppNotmem014Data
import NominalAlphaGlobal051ProofData001
import NominalAlphaRelease004Coarse052
import NominalAlphaRelease004Coarse053
import NominalAlphaRelease004Coarse054
import NominalAlphaRelease004Coarse055
import NominalAlphaRelease004Coarse056
import NominalAlphaRelease004Coarse057
import NominalAlphaRelease004Coarse058
import NominalAlphaRelease004Coarse059
import NominalAlphaRelease004Coarse060
import NominalAlphaRelease004Coarse061
import NominalAlphaRelease004Coarse062
import NominalAlphaRelease004Coarse063
import NominalAlphaRelease004Coarse064
import NominalAlphaRelease004Coarse065
import NominalAlphaRelease004Coarse066
import NominalAlphaRelease004Coarse067
import NominalAlphaRelease004Coarse068
import NominalAlphaRelease004Coarse069
import NominalAlphaRelease004Coarse070
import NominalAlphaRelease004Coarse071
import NominalAlphaRelease004Coarse072
import NominalAlphaRelease004Coarse073
import NominalAlphaRelease004Coarse074
import NominalAlphaRelease004Coarse075
import NominalAlphaRelease004Coarse076
import NominalAlphaRelease004Coarse077
import NominalAlphaRelease004Coarse078
import NominalAlphaRelease004Coarse079
import NominalAlphaRelease004Coarse080
import NominalAlphaRelease004Coarse081
import NominalAlphaRelease004Coarse082
import NominalAlphaRelease004Coarse083
import NominalAlphaRelease004Coarse084
import NominalAlphaRelease004Coarse085
import NominalAlphaRelease004Coarse086
import NominalAlphaRelease004Coarse087
import NominalAlphaHygieneV5Probe088
import NominalAlphaRelease004Coarse089
import NominalAlphaRelease004Coarse090
import NominalAlphaHygieneV5Coalesced091B
import NominalAlphaHygieneV5Coalesced092
import NominalAlphaHygieneV5Coalesced093
import NominalAlphaHygieneV5Coalesced094
import NominalAlphaHygieneV5Coalesced095
import NominalAlphaHygieneV5Coalesced096
import NominalAlphaHygieneV5Coalesced097
import NominalNFLiteralBaseFour
import NominalNFLiteralXpViaCompletenessDev003
import NominalNFLiteralRemainingViaCompletenessDev001
import NominalDefinitionLeafHandlersCanonical001
import NominalDefinitionLeafHandlersObjExtCompat001
import NominalRecanonTransportCompat001
import NominalWPPReplayChunk015Compact001Part041

set_option maxRecDepth 20000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

noncomputable def g_weisouniquecl
    (D : Class) (R : Class) (S : Class) (E : Class) (F : Class) (G : Class) (hyp_weisouniquecl_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_weisouniquecl_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classEq F G)) := by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ E.fv ∪ F.fv ∪ G.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport := by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (D).fv := by
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_D, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (F).fv := by
    clear dv_cache_0001
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (G).fv := by
    clear dv_cache_0001 dv_cache_0002
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_G, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)))).fv := by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (by
      have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) := by
        intro hmem
        cases hmem
      simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_not_F, fresh_x_not_G, fresh_x_not_D, fresh_x_not_E, fresh_x_not_R, fresh_x_not_S, compact_fv_not_mem_empty, false_or, or_false, true_and, and_true, false_and, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))
  have p0001 :=
    @g_simpl (syn_wiso F R S D E) (syn_wiso G R S D E)
  have p0002 :=
    @g_syl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)) (syn_wiso F R S D E) p0000 p0001
  have p0003 :=
    @g_isof1o D E R S F
  have p0004 :=
    @g_syl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wiso F R S D E) (syn_wf1o F D E) p0002 p0003
  have p0005 :=
    @g_f1ofn D E F
  have p0006 :=
    @g_syl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wf1o F D E) (syn_wfn F D) p0004 p0005
  have p0007 :=
    @g_simpr (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))
  have p0008 :=
    @g_simpr (syn_wiso F R S D E) (syn_wiso G R S D E)
  have p0009 :=
    @g_syl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)) (syn_wiso G R S D E) p0007 p0008
  have p0010 :=
    @g_isof1o D E R S G
  have p0011 :=
    @g_syl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wiso G R S D E) (syn_wf1o G D E) p0009 p0010
  have p0012 :=
    @g_f1ofn D E G
  have p0013 :=
    @g_syl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wf1o G D E) (syn_wfn G D) p0011 p0012
  have p0014 :=
    @g_simpl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)
  have p0015 :=
    @g_simpr (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))
  have p0016 :=
    @g_simpl (syn_wiso F R S D E) (syn_wiso G R S D E)
  have p0017 :=
    @g_syl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)) (syn_wiso F R S D E) p0015 p0016
  have p0018 :=
    @g_isof1o D E R S F
  have p0019 :=
    @g_syl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wiso F R S D E) (syn_wf1o F D E) p0017 p0018
  have p0020 :=
    @g_f1of D E F
  have p0021 :=
    @g_syl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wf1o F D E) (syn_wf F D E) p0019 p0020
  have p0022 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wf F D E) p0014 p0021
  have p0023 :=
    @g_simpr (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)
  have p0024 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wf F D E) (.classMem (.cv x) D) p0022 p0023
  have p0025 :=
    @g_ffvelrn D E (.cv x) F
  have p0026 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (syn_wf F D E) (.classMem (.cv x) D)) (.classMem (syn_cfv F (.cv x)) E) p0024 p0025
  have p0027 :=
    @g_simpl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)
  have p0028 :=
    @g_simpr (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))
  have p0029 :=
    @g_simpr (syn_wiso F R S D E) (syn_wiso G R S D E)
  have p0030 :=
    @g_syl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)) (syn_wiso G R S D E) p0028 p0029
  have p0031 :=
    @g_isof1o D E R S G
  have p0032 :=
    @g_syl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wiso G R S D E) (syn_wf1o G D E) p0030 p0031
  have p0033 :=
    @g_f1of D E G
  have p0034 :=
    @g_syl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wf1o G D E) (syn_wf G D E) p0032 p0033
  have p0035 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wf G D E) p0027 p0034
  have p0036 :=
    @g_simpr (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)
  have p0037 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wf G D E) (.classMem (.cv x) D) p0035 p0036
  have p0038 :=
    @g_ffvelrn D E (.cv x) G
  have p0039 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (syn_wf G D E) (.classMem (.cv x) D)) (.classMem (syn_cfv G (.cv x)) E) p0037 p0038
  have p0040 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (.classMem (syn_cfv F (.cv x)) E) (.classMem (syn_cfv G (.cv x)) E) p0026 p0039
  have p0041 :=
    @g_simpl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)
  have p0042 :=
    @g_simpl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))
  have p0043 :=
    @g_simpr (.classMem F (syn_cvv)) (.classMem G (syn_cvv))
  have p0044 :=
    @g_syl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (.classMem G (syn_cvv)) p0042 p0043
  have p0045 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem G (syn_cvv)) p0041 p0044
  have p0046 :=
    @g_brex R D (syn_cwe)
  have p0047 :=
    Nominal.mp hyp_weisouniquecl_1 p0046
  have p0048 :=
    @g_simpr (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0049 :=
    Nominal.mp p0047 p0048
  have p0050 :=
    @g_brex R D (syn_cwe)
  have p0051 :=
    Nominal.mp hyp_weisouniquecl_1 p0050
  have p0052 :=
    @g_simpl (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0053 :=
    Nominal.mp p0051 p0052
  have p0054 :=
    @g_idex
  have p0055 :=
    @g_difex R (syn_cid) p0053 p0054
  have p0056 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0055
  have p0057 :=
    @g_snex (.cv x)
  have p0058 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0056 p0057
  have p0059 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0049 p0058
  have p0060 :=
    @g_a1i (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) p0059
  have p0061 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (.classMem G (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p0045 p0060
  have p0062 :=
    @g_resexg G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv) (syn_cvv)
  have p0063 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (.classMem G (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv))) (.classMem (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv)) p0061 p0062
  have p0064 :=
    @g_simpl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)
  have p0065 :=
    @g_simpl (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))
  have p0066 :=
    @g_simpl (.classMem F (syn_cvv)) (.classMem G (syn_cvv))
  have p0067 :=
    @g_syl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (.classMem F (syn_cvv)) p0065 p0066
  have p0068 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem F (syn_cvv)) p0064 p0067
  have p0069 :=
    @g_brex R D (syn_cwe)
  have p0070 :=
    Nominal.mp hyp_weisouniquecl_1 p0069
  have p0071 :=
    @g_simpr (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0072 :=
    Nominal.mp p0070 p0071
  have p0073 :=
    @g_brex R D (syn_cwe)
  have p0074 :=
    Nominal.mp hyp_weisouniquecl_1 p0073
  have p0075 :=
    @g_simpl (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0076 :=
    Nominal.mp p0074 p0075
  have p0077 :=
    @g_idex
  have p0078 :=
    @g_difex R (syn_cid) p0076 p0077
  have p0079 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0078
  have p0080 :=
    @g_snex (.cv x)
  have p0081 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0079 p0080
  have p0082 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0072 p0081
  have p0083 :=
    @g_a1i (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) p0082
  have p0084 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (.classMem F (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv)) p0068 p0083
  have p0085 :=
    @g_resexg F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv) (syn_cvv)
  have p0086 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (.classMem F (syn_cvv)) (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cvv))) (.classMem (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv)) p0084 p0085
  have p0087 :=
    @g_cnvexg (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv)
  have p0088 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (.classMem (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv)) (.classMem (syn_ccnv (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cvv)) p0086 p0087
  have p0089 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (.classMem (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv)) (.classMem (syn_ccnv (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cvv)) p0063 p0088
  have p0090 :=
    @g_coexg (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_ccnv (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cvv) (syn_cvv)
  have p0091 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (.classMem (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cvv)) (.classMem (syn_ccnv (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cvv))) (.classMem (syn_ccom (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_ccnv (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cvv)) p0089 p0090
  have p0092 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (.classMem (syn_cfv F (.cv x)) E) (.classMem (syn_cfv G (.cv x)) E)) (.classMem (syn_ccom (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_ccnv (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cvv)) p0040 p0091
  have p0093 :=
    @g_simpl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)
  have p0094 :=
    @g_simpr (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))
  have p0095 :=
    @g_simpl (syn_wiso F R S D E) (syn_wiso G R S D E)
  have p0096 :=
    @g_syl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)) (syn_wiso F R S D E) p0094 p0095
  have p0097 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wiso F R S D E) p0093 p0096
  have p0098 :=
    @g_simpr (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)
  have p0099 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wiso F R S D E) (.classMem (.cv x) D) p0097 p0098
  have p0100 :=
    @g_isostrictsegresndv x D R S E F
  have p0101 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (syn_wiso F R S D E) (.classMem (.cv x) D)) (syn_wiso (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))) p0099 p0100
  have p0102 :=
    @g_isocnv (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))))) (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0103 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wiso (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x)))))) (syn_wiso (syn_ccnv (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) p0101 p0102
  have p0104 :=
    @g_simpl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)
  have p0105 :=
    @g_simpr (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))
  have p0106 :=
    @g_simpr (syn_wiso F R S D E) (syn_wiso G R S D E)
  have p0107 :=
    @g_syl (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E)) (syn_wiso G R S D E) p0105 p0106
  have p0108 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (syn_wiso G R S D E) p0104 p0107
  have p0109 :=
    @g_simpr (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)
  have p0110 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wiso G R S D E) (.classMem (.cv x) D) p0108 p0109
  have p0111 :=
    @g_isostrictsegresndv x D R S E G
  have p0112 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (syn_wiso G R S D E) (.classMem (.cv x) D)) (syn_wiso (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x)))))) p0110 p0111
  have p0113 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wiso (syn_ccnv (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x)))))) p0103 p0112
  have p0114 :=
    @g_isotr (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))))) (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_ccnv (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
  have p0115 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (syn_wiso (syn_ccnv (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))))) (syn_wiso (syn_ccom (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_ccnv (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x)))))) p0113 p0114
  have p0116 :=
    @g_jca (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (syn_wa (.classMem (syn_cfv F (.cv x)) E) (.classMem (syn_cfv G (.cv x)) E)) (.classMem (syn_ccom (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_ccnv (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cvv))) (syn_wiso (syn_ccom (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_ccnv (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x)))))) p0092 p0115
  have p0117 :=
    @g_wecutisoendpointseqclndv (syn_cfv F (.cv x)) (syn_cfv G (.cv x)) E S (syn_ccom (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_ccnv (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) hyp_weisouniquecl_2
  have p0118 :=
    @g_syl (syn_wa (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) (.classMem (.cv x) D)) (syn_wa (syn_wa (syn_wa (.classMem (syn_cfv F (.cv x)) E) (.classMem (syn_cfv G (.cv x)) E)) (.classMem (syn_ccom (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_ccnv (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cvv))) (syn_wiso (syn_ccom (syn_cres G (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_ccnv (syn_cres F (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv F (.cv x))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (syn_cfv G (.cv x))))))) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))) p0116 p0117
  have p0119 :=
    @g_eqfnfvd (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F R S D E) (syn_wiso G R S D E))) x D F G dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0006 p0013 p0118
  exact p0119

noncomputable def g_wecutisouniquecl
    (B : Class) (C : Class) (D : Class) (R : Class) (S : Class) (E : Class) (F : Class) (G : Class) (hyp_wecutisouniquecl_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) (hyp_wecutisouniquecl_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (.classMem F (syn_cvv)) (.classMem G (syn_cvv))) (syn_wa (syn_wiso F (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C)))) (syn_wiso G (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C)))))) (.classEq F G)) := by
  let proofSupport : Finset Var := B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv ∪ F.fv ∪ G.fv
  have p0000 :=
    @g_id (syn_wbr R (syn_cwe) D)
  have p0001 :=
    @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))
  have p0002 :=
    @g_a1i (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) D) (syn_wbr R (syn_cwe) D) p0001
  have p0003 :=
    @g_brex R D (syn_cwe)
  have p0004 :=
    Nominal.mp hyp_wecutisouniquecl_1 p0003
  have p0005 :=
    @g_simpr (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0006 :=
    Nominal.mp p0004 p0005
  have p0007 :=
    @g_brex R D (syn_cwe)
  have p0008 :=
    Nominal.mp hyp_wecutisouniquecl_1 p0007
  have p0009 :=
    @g_simpl (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
  have p0010 :=
    Nominal.mp p0008 p0009
  have p0011 :=
    @g_idex
  have p0012 :=
    @g_difex R (syn_cid) p0010 p0011
  have p0013 :=
    @g_cnvex (syn_cdif R (syn_cid)) p0012
  have p0014 :=
    @g_snex B
  have p0015 :=
    @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B) p0013 p0014
  have p0016 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)) p0006 p0015
  have p0017 :=
    @g_a1i (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cvv)) (syn_wbr R (syn_cwe) D) p0016
  have p0018 :=
    @g_werestrndv (syn_wbr R (syn_cwe) D) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) D R p0000 p0002 p0017
  have p0019 :=
    Nominal.mp hyp_wecutisouniquecl_1 p0018
  have p0020 :=
    @g_id (syn_wbr S (syn_cwe) E)
  have p0021 :=
    @g_inss1 E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))
  have p0022 :=
    @g_a1i (syn_wss (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))) E) (syn_wbr S (syn_cwe) E) p0021
  have p0023 :=
    @g_brex S E (syn_cwe)
  have p0024 :=
    Nominal.mp hyp_wecutisouniquecl_2 p0023
  have p0025 :=
    @g_simpr (.classMem S (syn_cvv)) (.classMem E (syn_cvv))
  have p0026 :=
    Nominal.mp p0024 p0025
  have p0027 :=
    @g_brex S E (syn_cwe)
  have p0028 :=
    Nominal.mp hyp_wecutisouniquecl_2 p0027
  have p0029 :=
    @g_simpl (.classMem S (syn_cvv)) (.classMem E (syn_cvv))
  have p0030 :=
    Nominal.mp p0028 p0029
  have p0031 :=
    @g_idex
  have p0032 :=
    @g_difex S (syn_cid) p0030 p0031
  have p0033 :=
    @g_cnvex (syn_cdif S (syn_cid)) p0032
  have p0034 :=
    @g_snex C
  have p0035 :=
    @g_imaex (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C) p0033 p0034
  have p0036 :=
    @g_inex E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C)) p0026 p0035
  have p0037 :=
    @g_a1i (.classMem (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))) (syn_cvv)) (syn_wbr S (syn_cwe) E) p0036
  have p0038 :=
    @g_werestrndv (syn_wbr S (syn_cwe) E) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))) E S p0020 p0022 p0037
  have p0039 :=
    Nominal.mp hyp_wecutisouniquecl_2 p0038
  have p0040 :=
    @g_weisouniquecl (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))) (syn_cin S (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))))) (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn C))) F G p0019 p0039
  exact p0040

#print axioms g_wecutisouniquecl

end NFChoice.DirectNominalPrf.WPPReplay
