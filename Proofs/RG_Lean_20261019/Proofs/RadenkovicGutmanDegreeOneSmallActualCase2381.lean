/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2381 : Family 10 := level10.get ⟨1154,by decide⟩
def sourceMap2381 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,4,5,6,7,2,3] (sourceLabel 10 0 0 v)
def fusedMap2381 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2381_checked : acceptsGraphIso
    (source (graph core2381) (root 10) 0 0) DegreeOneSmallSpectrum1738.graph sourceMap2381=true := by decide +kernel
theorem fusedMap2381_checked : acceptsGraphIso
    (fused (graph core2381) (root 10) 0 0) DegreeOneSmallSpectrum1837.graph fusedMap2381=true := by decide +kernel
theorem certified2381 : Certified (graph core2381) (root 10) 0 0 :=
  of_native_maps core2381 DegreeOneSmallSpectrum1738.graph DegreeOneSmallSpectrum1837.graph
    sourceMap2381 fusedMap2381 sourceMap2381_checked fusedMap2381_checked
    DegreeOneSmallComparisons.comparison2381
#print axioms sourceMap2381_checked
#print axioms fusedMap2381_checked
#print axioms certified2381
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
