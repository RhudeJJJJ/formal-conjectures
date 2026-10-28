/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4928 : Family 10 := level10.get ⟨1438,by decide⟩
def sourceMap4928 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,8,9,10,11,12,13,14,15,16,7,1,2,3,4,5,6] (sourceLabel 10 2 2 v)
def fusedMap4928 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4928_checked : acceptsGraphIso
    (source (graph core4928) (root 10) 2 2) DegreeTwoThreeSpectrum7528.graph sourceMap4928=true := by decide +kernel
theorem fusedMap4928_checked : acceptsGraphIso
    (fused (graph core4928) (root 10) 2 2) DegreeTwoThreeSpectrum6897.graph fusedMap4928=true := by decide +kernel
theorem certified4928 : Certified (graph core4928) (root 10) 2 2 :=
  of_native_maps core4928 DegreeTwoThreeSpectrum7528.graph DegreeTwoThreeSpectrum6897.graph
    sourceMap4928 fusedMap4928 sourceMap4928_checked fusedMap4928_checked
    DegreeTwoThreeFiniteComparisons.comparison4928
#print axioms sourceMap4928_checked
#print axioms fusedMap4928_checked
#print axioms certified4928
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
