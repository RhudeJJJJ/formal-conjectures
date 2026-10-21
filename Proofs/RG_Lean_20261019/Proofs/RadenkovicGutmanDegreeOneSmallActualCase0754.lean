/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0754 : Family 8 := level8.get ⟨4,by decide⟩
def sourceMap0754 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0754 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0754_checked : acceptsGraphIso
    (source (graph core0754) (root 8) 1 1) DegreeOneSmallSpectrum914.graph sourceMap0754=true := by decide +kernel
theorem fusedMap0754_checked : acceptsGraphIso
    (fused (graph core0754) (root 8) 1 1) DegreeOneSmallSpectrum859.graph fusedMap0754=true := by decide +kernel
theorem certified0754 : Certified (graph core0754) (root 8) 1 1 :=
  of_native_maps core0754 DegreeOneSmallSpectrum914.graph DegreeOneSmallSpectrum859.graph
    sourceMap0754 fusedMap0754 sourceMap0754_checked fusedMap0754_checked
    DegreeOneSmallComparisons.comparison0754
#print axioms sourceMap0754_checked
#print axioms fusedMap0754_checked
#print axioms certified0754
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
