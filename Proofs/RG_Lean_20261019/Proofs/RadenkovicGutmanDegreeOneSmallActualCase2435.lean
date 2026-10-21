/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2435 : Family 10 := level10.get ⟨1353,by decide⟩
def sourceMap2435 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,9,10,11,12,1,2,3,4,8,6,7] (sourceLabel 10 0 0 v)
def fusedMap2435 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2435_checked : acceptsGraphIso
    (source (graph core2435) (root 10) 0 0) DegreeOneSmallSpectrum1608.graph sourceMap2435=true := by decide +kernel
theorem fusedMap2435_checked : acceptsGraphIso
    (fused (graph core2435) (root 10) 0 0) DegreeOneSmallSpectrum1966.graph fusedMap2435=true := by decide +kernel
theorem certified2435 : Certified (graph core2435) (root 10) 0 0 :=
  of_native_maps core2435 DegreeOneSmallSpectrum1608.graph DegreeOneSmallSpectrum1966.graph
    sourceMap2435 fusedMap2435 sourceMap2435_checked fusedMap2435_checked
    DegreeOneSmallComparisons.comparison2435
#print axioms sourceMap2435_checked
#print axioms fusedMap2435_checked
#print axioms certified2435
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
