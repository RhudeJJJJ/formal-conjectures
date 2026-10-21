/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2367 : Family 10 := level10.get ⟨1126,by decide⟩
def sourceMap2367 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2367 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2367_checked : acceptsGraphIso
    (source (graph core2367) (root 10) 0 0) DegreeOneSmallSpectrum1775.graph sourceMap2367=true := by decide +kernel
theorem fusedMap2367_checked : acceptsGraphIso
    (fused (graph core2367) (root 10) 0 0) DegreeOneSmallSpectrum1777.graph fusedMap2367=true := by decide +kernel
theorem certified2367 : Certified (graph core2367) (root 10) 0 0 :=
  of_native_maps core2367 DegreeOneSmallSpectrum1775.graph DegreeOneSmallSpectrum1777.graph
    sourceMap2367 fusedMap2367 sourceMap2367_checked fusedMap2367_checked
    DegreeOneSmallComparisons.comparison2367
#print axioms sourceMap2367_checked
#print axioms fusedMap2367_checked
#print axioms certified2367
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
