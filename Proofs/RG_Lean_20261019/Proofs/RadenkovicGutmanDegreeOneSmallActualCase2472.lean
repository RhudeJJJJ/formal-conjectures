/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2472 : Family 10 := level10.get ⟨1575,by decide⟩
def sourceMap2472 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (sourceLabel 10 0 0 v)
def fusedMap2472 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2472_checked : acceptsGraphIso
    (source (graph core2472) (root 10) 0 0) DegreeOneSmallSpectrum2007.graph sourceMap2472=true := by decide +kernel
theorem fusedMap2472_checked : acceptsGraphIso
    (fused (graph core2472) (root 10) 0 0) DegreeOneSmallSpectrum1621.graph fusedMap2472=true := by decide +kernel
theorem certified2472 : Certified (graph core2472) (root 10) 0 0 :=
  of_native_maps core2472 DegreeOneSmallSpectrum2007.graph DegreeOneSmallSpectrum1621.graph
    sourceMap2472 fusedMap2472 sourceMap2472_checked fusedMap2472_checked
    DegreeOneSmallComparisons.comparison2472
#print axioms sourceMap2472_checked
#print axioms fusedMap2472_checked
#print axioms certified2472
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
