/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2358 : Family 10 := level10.get ⟨1104,by decide⟩
def sourceMap2358 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2358 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2358_checked : acceptsGraphIso
    (source (graph core2358) (root 10) 0 0) DegreeOneSmallSpectrum1728.graph sourceMap2358=true := by decide +kernel
theorem fusedMap2358_checked : acceptsGraphIso
    (fused (graph core2358) (root 10) 0 0) DegreeOneSmallSpectrum1733.graph fusedMap2358=true := by decide +kernel
theorem certified2358 : Certified (graph core2358) (root 10) 0 0 :=
  of_native_maps core2358 DegreeOneSmallSpectrum1728.graph DegreeOneSmallSpectrum1733.graph
    sourceMap2358 fusedMap2358 sourceMap2358_checked fusedMap2358_checked
    DegreeOneSmallComparisons.comparison2358
#print axioms sourceMap2358_checked
#print axioms fusedMap2358_checked
#print axioms certified2358
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
