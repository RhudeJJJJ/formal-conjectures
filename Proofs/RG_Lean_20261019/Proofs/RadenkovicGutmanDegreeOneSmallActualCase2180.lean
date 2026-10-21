/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2180 : Family 10 := level10.get ⟨662,by decide⟩
def sourceMap2180 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2180 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2180_checked : acceptsGraphIso
    (source (graph core2180) (root 10) 0 0) DegreeOneSmallSpectrum1739.graph sourceMap2180=true := by decide +kernel
theorem fusedMap2180_checked : acceptsGraphIso
    (fused (graph core2180) (root 10) 0 0) DegreeOneSmallSpectrum1280.graph fusedMap2180=true := by decide +kernel
theorem certified2180 : Certified (graph core2180) (root 10) 0 0 :=
  of_native_maps core2180 DegreeOneSmallSpectrum1739.graph DegreeOneSmallSpectrum1280.graph
    sourceMap2180 fusedMap2180 sourceMap2180_checked fusedMap2180_checked
    DegreeOneSmallComparisons.comparison2180
#print axioms sourceMap2180_checked
#print axioms fusedMap2180_checked
#print axioms certified2180
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
