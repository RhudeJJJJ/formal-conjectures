/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4268 : Family 9 := level9.get ⟨269,by decide⟩
def sourceMap4268 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4268 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4268_checked : acceptsGraphIso
    (source (graph core4268) (root 9) 2 2) DegreeTwoThreeSpectrum4892.graph sourceMap4268=true := by decide +kernel
theorem fusedMap4268_checked : acceptsGraphIso
    (fused (graph core4268) (root 9) 2 2) DegreeTwoThreeSpectrum4082.graph fusedMap4268=true := by decide +kernel
theorem certified4268 : Certified (graph core4268) (root 9) 2 2 :=
  of_native_maps core4268 DegreeTwoThreeSpectrum4892.graph DegreeTwoThreeSpectrum4082.graph
    sourceMap4268 fusedMap4268 sourceMap4268_checked fusedMap4268_checked
    DegreeTwoThreeFiniteComparisons.comparison4268
#print axioms sourceMap4268_checked
#print axioms fusedMap4268_checked
#print axioms certified4268
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
