/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2468 : Family 10 := level10.get ⟨1566,by decide⟩
def sourceMap2468 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2468 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2468_checked : acceptsGraphIso
    (source (graph core2468) (root 10) 0 0) DegreeOneSmallSpectrum2003.graph sourceMap2468=true := by decide +kernel
theorem fusedMap2468_checked : acceptsGraphIso
    (fused (graph core2468) (root 10) 0 0) DegreeOneSmallSpectrum1601.graph fusedMap2468=true := by decide +kernel
theorem certified2468 : Certified (graph core2468) (root 10) 0 0 :=
  of_native_maps core2468 DegreeOneSmallSpectrum2003.graph DegreeOneSmallSpectrum1601.graph
    sourceMap2468 fusedMap2468 sourceMap2468_checked fusedMap2468_checked
    DegreeOneSmallComparisons.comparison2468
#print axioms sourceMap2468_checked
#print axioms fusedMap2468_checked
#print axioms certified2468
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
