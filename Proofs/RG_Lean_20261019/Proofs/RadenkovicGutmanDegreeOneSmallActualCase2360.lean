/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2360 : Family 10 := level10.get ⟨1107,by decide⟩
def sourceMap2360 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2360 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2360_checked : acceptsGraphIso
    (source (graph core2360) (root 10) 0 0) DegreeOneSmallSpectrum1738.graph sourceMap2360=true := by decide +kernel
theorem fusedMap2360_checked : acceptsGraphIso
    (fused (graph core2360) (root 10) 0 0) DegreeOneSmallSpectrum1743.graph fusedMap2360=true := by decide +kernel
theorem certified2360 : Certified (graph core2360) (root 10) 0 0 :=
  of_native_maps core2360 DegreeOneSmallSpectrum1738.graph DegreeOneSmallSpectrum1743.graph
    sourceMap2360 fusedMap2360 sourceMap2360_checked fusedMap2360_checked
    DegreeOneSmallComparisons.comparison2360
#print axioms sourceMap2360_checked
#print axioms fusedMap2360_checked
#print axioms certified2360
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
