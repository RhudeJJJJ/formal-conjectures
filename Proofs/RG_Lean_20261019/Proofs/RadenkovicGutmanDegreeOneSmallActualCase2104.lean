/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2104 : Family 10 := level10.get ⟨525,by decide⟩
def sourceMap2104 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2104 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2104_checked : acceptsGraphIso
    (source (graph core2104) (root 10) 0 0) DegreeOneSmallSpectrum1661.graph sourceMap2104=true := by decide +kernel
theorem fusedMap2104_checked : acceptsGraphIso
    (fused (graph core2104) (root 10) 0 0) DegreeOneSmallSpectrum1022.graph fusedMap2104=true := by decide +kernel
theorem certified2104 : Certified (graph core2104) (root 10) 0 0 :=
  of_native_maps core2104 DegreeOneSmallSpectrum1661.graph DegreeOneSmallSpectrum1022.graph
    sourceMap2104 fusedMap2104 sourceMap2104_checked fusedMap2104_checked
    DegreeOneSmallComparisons.comparison2104
#print axioms sourceMap2104_checked
#print axioms fusedMap2104_checked
#print axioms certified2104
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
