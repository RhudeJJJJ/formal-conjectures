/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2466 : Family 10 := level10.get ⟨1546,by decide⟩
def sourceMap2466 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (sourceLabel 10 0 0 v)
def fusedMap2466 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2466_checked : acceptsGraphIso
    (source (graph core2466) (root 10) 0 0) DegreeOneSmallSpectrum2001.graph sourceMap2466=true := by decide +kernel
theorem fusedMap2466_checked : acceptsGraphIso
    (fused (graph core2466) (root 10) 0 0) DegreeOneSmallSpectrum1560.graph fusedMap2466=true := by decide +kernel
theorem certified2466 : Certified (graph core2466) (root 10) 0 0 :=
  of_native_maps core2466 DegreeOneSmallSpectrum2001.graph DegreeOneSmallSpectrum1560.graph
    sourceMap2466 fusedMap2466 sourceMap2466_checked fusedMap2466_checked
    DegreeOneSmallComparisons.comparison2466
#print axioms sourceMap2466_checked
#print axioms fusedMap2466_checked
#print axioms certified2466
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
