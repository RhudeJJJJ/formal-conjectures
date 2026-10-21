/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2426 : Family 10 := level10.get ⟨1320,by decide⟩
def sourceMap2426 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,8,9,10,11,12,1,2,3,4,6,7] (sourceLabel 10 0 0 v)
def fusedMap2426 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2426_checked : acceptsGraphIso
    (source (graph core2426) (root 10) 0 0) DegreeOneSmallSpectrum1614.graph sourceMap2426=true := by decide +kernel
theorem fusedMap2426_checked : acceptsGraphIso
    (fused (graph core2426) (root 10) 0 0) DegreeOneSmallSpectrum1951.graph fusedMap2426=true := by decide +kernel
theorem certified2426 : Certified (graph core2426) (root 10) 0 0 :=
  of_native_maps core2426 DegreeOneSmallSpectrum1614.graph DegreeOneSmallSpectrum1951.graph
    sourceMap2426 fusedMap2426 sourceMap2426_checked fusedMap2426_checked
    DegreeOneSmallComparisons.comparison2426
#print axioms sourceMap2426_checked
#print axioms fusedMap2426_checked
#print axioms certified2426
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
