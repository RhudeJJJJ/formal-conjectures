/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2436 : Family 10 := level10.get ⟨1355,by decide⟩
def sourceMap2436 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,4,5,6,7,8,2,3] (sourceLabel 10 0 0 v)
def fusedMap2436 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2436_checked : acceptsGraphIso
    (source (graph core2436) (root 10) 0 0) DegreeOneSmallSpectrum1700.graph sourceMap2436=true := by decide +kernel
theorem fusedMap2436_checked : acceptsGraphIso
    (fused (graph core2436) (root 10) 0 0) DegreeOneSmallSpectrum1967.graph fusedMap2436=true := by decide +kernel
theorem certified2436 : Certified (graph core2436) (root 10) 0 0 :=
  of_native_maps core2436 DegreeOneSmallSpectrum1700.graph DegreeOneSmallSpectrum1967.graph
    sourceMap2436 fusedMap2436 sourceMap2436_checked fusedMap2436_checked
    DegreeOneSmallComparisons.comparison2436
#print axioms sourceMap2436_checked
#print axioms fusedMap2436_checked
#print axioms certified2436
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
