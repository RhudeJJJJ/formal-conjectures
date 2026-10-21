/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2390 : Family 10 := level10.get ⟨1187,by decide⟩
def sourceMap2390 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,9,10,11,12,1,2,3,4,8,6,7] (sourceLabel 10 0 0 v)
def fusedMap2390 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2390_checked : acceptsGraphIso
    (source (graph core2390) (root 10) 0 0) DegreeOneSmallSpectrum1607.graph sourceMap2390=true := by decide +kernel
theorem fusedMap2390_checked : acceptsGraphIso
    (fused (graph core2390) (root 10) 0 0) DegreeOneSmallSpectrum1879.graph fusedMap2390=true := by decide +kernel
theorem certified2390 : Certified (graph core2390) (root 10) 0 0 :=
  of_native_maps core2390 DegreeOneSmallSpectrum1607.graph DegreeOneSmallSpectrum1879.graph
    sourceMap2390 fusedMap2390 sourceMap2390_checked fusedMap2390_checked
    DegreeOneSmallComparisons.comparison2390
#print axioms sourceMap2390_checked
#print axioms fusedMap2390_checked
#print axioms certified2390
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
