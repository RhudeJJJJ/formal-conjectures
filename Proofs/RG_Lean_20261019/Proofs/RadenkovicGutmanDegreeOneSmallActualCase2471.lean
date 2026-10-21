/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2471 : Family 10 := level10.get ⟨1573,by decide⟩
def sourceMap2471 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (sourceLabel 10 0 0 v)
def fusedMap2471 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2471_checked : acceptsGraphIso
    (source (graph core2471) (root 10) 0 0) DegreeOneSmallSpectrum2006.graph sourceMap2471=true := by decide +kernel
theorem fusedMap2471_checked : acceptsGraphIso
    (fused (graph core2471) (root 10) 0 0) DegreeOneSmallSpectrum1617.graph fusedMap2471=true := by decide +kernel
theorem certified2471 : Certified (graph core2471) (root 10) 0 0 :=
  of_native_maps core2471 DegreeOneSmallSpectrum2006.graph DegreeOneSmallSpectrum1617.graph
    sourceMap2471 fusedMap2471 sourceMap2471_checked fusedMap2471_checked
    DegreeOneSmallComparisons.comparison2471
#print axioms sourceMap2471_checked
#print axioms fusedMap2471_checked
#print axioms certified2471
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
