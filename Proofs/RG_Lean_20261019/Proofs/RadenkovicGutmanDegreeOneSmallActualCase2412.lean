/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2412 : Family 10 := level10.get ⟨1273,by decide⟩
def sourceMap2412 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,4,5,6,7,2,3] (sourceLabel 10 0 0 v)
def fusedMap2412 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2412_checked : acceptsGraphIso
    (source (graph core2412) (root 10) 0 0) DegreeOneSmallSpectrum1708.graph sourceMap2412=true := by decide +kernel
theorem fusedMap2412_checked : acceptsGraphIso
    (fused (graph core2412) (root 10) 0 0) DegreeOneSmallSpectrum1928.graph fusedMap2412=true := by decide +kernel
theorem certified2412 : Certified (graph core2412) (root 10) 0 0 :=
  of_native_maps core2412 DegreeOneSmallSpectrum1708.graph DegreeOneSmallSpectrum1928.graph
    sourceMap2412 fusedMap2412 sourceMap2412_checked fusedMap2412_checked
    DegreeOneSmallComparisons.comparison2412
#print axioms sourceMap2412_checked
#print axioms fusedMap2412_checked
#print axioms certified2412
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
