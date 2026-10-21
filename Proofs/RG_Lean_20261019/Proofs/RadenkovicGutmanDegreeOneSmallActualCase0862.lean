/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0862 : Family 8 := level8.get ⟨40,by decide⟩
def sourceMap0862 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0862 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0862_checked : acceptsGraphIso
    (source (graph core0862) (root 8) 1 1) DegreeOneSmallSpectrum1128.graph sourceMap0862=true := by decide +kernel
theorem fusedMap0862_checked : acceptsGraphIso
    (fused (graph core0862) (root 8) 1 1) DegreeOneSmallSpectrum872.graph fusedMap0862=true := by decide +kernel
theorem certified0862 : Certified (graph core0862) (root 8) 1 1 :=
  of_native_maps core0862 DegreeOneSmallSpectrum1128.graph DegreeOneSmallSpectrum872.graph
    sourceMap0862 fusedMap0862 sourceMap0862_checked fusedMap0862_checked
    DegreeOneSmallComparisons.comparison0862
#print axioms sourceMap0862_checked
#print axioms fusedMap0862_checked
#print axioms certified0862
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
