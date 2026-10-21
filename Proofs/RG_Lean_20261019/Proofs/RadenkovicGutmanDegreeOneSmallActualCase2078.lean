/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2078 : Family 10 := level10.get ⟨470,by decide⟩
def sourceMap2078 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,1,0,9,10,11,12,2,3,4,8,6,7] (sourceLabel 10 0 0 v)
def fusedMap2078 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2078_checked : acceptsGraphIso
    (source (graph core2078) (root 10) 0 0) DegreeOneSmallSpectrum1471.graph sourceMap2078=true := by decide +kernel
theorem fusedMap2078_checked : acceptsGraphIso
    (fused (graph core2078) (root 10) 0 0) DegreeOneSmallSpectrum1459.graph fusedMap2078=true := by decide +kernel
theorem certified2078 : Certified (graph core2078) (root 10) 0 0 :=
  of_native_maps core2078 DegreeOneSmallSpectrum1471.graph DegreeOneSmallSpectrum1459.graph
    sourceMap2078 fusedMap2078 sourceMap2078_checked fusedMap2078_checked
    DegreeOneSmallComparisons.comparison2078
#print axioms sourceMap2078_checked
#print axioms fusedMap2078_checked
#print axioms certified2078
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
