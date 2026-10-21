/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2475 : Family 10 := level10.get ⟨1615,by decide⟩
def sourceMap2475 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (sourceLabel 10 0 0 v)
def fusedMap2475 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2475_checked : acceptsGraphIso
    (source (graph core2475) (root 10) 0 0) DegreeOneSmallSpectrum2010.graph sourceMap2475=true := by decide +kernel
theorem fusedMap2475_checked : acceptsGraphIso
    (fused (graph core2475) (root 10) 0 0) DegreeOneSmallSpectrum1698.graph fusedMap2475=true := by decide +kernel
theorem certified2475 : Certified (graph core2475) (root 10) 0 0 :=
  of_native_maps core2475 DegreeOneSmallSpectrum2010.graph DegreeOneSmallSpectrum1698.graph
    sourceMap2475 fusedMap2475 sourceMap2475_checked fusedMap2475_checked
    DegreeOneSmallComparisons.comparison2475
#print axioms sourceMap2475_checked
#print axioms fusedMap2475_checked
#print axioms certified2475
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
