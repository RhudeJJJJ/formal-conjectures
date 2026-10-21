/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2482 : Family 10 := level10.get ⟨1701,by decide⟩
def sourceMap2482 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (sourceLabel 10 0 0 v)
def fusedMap2482 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2482_checked : acceptsGraphIso
    (source (graph core2482) (root 10) 0 0) DegreeOneSmallSpectrum2017.graph sourceMap2482=true := by decide +kernel
theorem fusedMap2482_checked : acceptsGraphIso
    (fused (graph core2482) (root 10) 0 0) DegreeOneSmallSpectrum1888.graph fusedMap2482=true := by decide +kernel
theorem certified2482 : Certified (graph core2482) (root 10) 0 0 :=
  of_native_maps core2482 DegreeOneSmallSpectrum2017.graph DegreeOneSmallSpectrum1888.graph
    sourceMap2482 fusedMap2482 sourceMap2482_checked fusedMap2482_checked
    DegreeOneSmallComparisons.comparison2482
#print axioms sourceMap2482_checked
#print axioms fusedMap2482_checked
#print axioms certified2482
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
