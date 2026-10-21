/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2450 : Family 10 := level10.get ⟨1426,by decide⟩
def sourceMap2450 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,10,11,12,4,5,6,7,8,9,2,3] (sourceLabel 10 0 0 v)
def fusedMap2450 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2450_checked : acceptsGraphIso
    (source (graph core2450) (root 10) 0 0) DegreeOneSmallSpectrum1698.graph sourceMap2450=true := by decide +kernel
theorem fusedMap2450_checked : acceptsGraphIso
    (fused (graph core2450) (root 10) 0 0) DegreeOneSmallSpectrum1981.graph fusedMap2450=true := by decide +kernel
theorem certified2450 : Certified (graph core2450) (root 10) 0 0 :=
  of_native_maps core2450 DegreeOneSmallSpectrum1698.graph DegreeOneSmallSpectrum1981.graph
    sourceMap2450 fusedMap2450 sourceMap2450_checked fusedMap2450_checked
    DegreeOneSmallComparisons.comparison2450
#print axioms sourceMap2450_checked
#print axioms fusedMap2450_checked
#print axioms certified2450
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
