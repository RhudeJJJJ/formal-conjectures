/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2039 : Family 10 := level10.get ⟨396,by decide⟩
def sourceMap2039 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2039 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2039_checked : acceptsGraphIso
    (source (graph core2039) (root 10) 0 0) DegreeOneSmallSpectrum1156.graph sourceMap2039=true := by decide +kernel
theorem fusedMap2039_checked : acceptsGraphIso
    (fused (graph core2039) (root 10) 0 0) DegreeOneSmallSpectrum1499.graph fusedMap2039=true := by decide +kernel
theorem certified2039 : Certified (graph core2039) (root 10) 0 0 :=
  of_native_maps core2039 DegreeOneSmallSpectrum1156.graph DegreeOneSmallSpectrum1499.graph
    sourceMap2039 fusedMap2039 sourceMap2039_checked fusedMap2039_checked
    DegreeOneSmallComparisons.comparison2039
#print axioms sourceMap2039_checked
#print axioms fusedMap2039_checked
#print axioms certified2039
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
