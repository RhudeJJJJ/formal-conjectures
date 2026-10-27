/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4281 : Family 9 := level9.get ⟨302,by decide⟩
def sourceMap4281 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,8,9,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4281 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4281_checked : acceptsGraphIso
    (source (graph core4281) (root 9) 2 2) DegreeTwoThreeSpectrum4881.graph sourceMap4281=true := by decide +kernel
theorem fusedMap4281_checked : acceptsGraphIso
    (fused (graph core4281) (root 9) 2 2) DegreeTwoThreeSpectrum4134.graph fusedMap4281=true := by decide +kernel
theorem certified4281 : Certified (graph core4281) (root 9) 2 2 :=
  of_native_maps core4281 DegreeTwoThreeSpectrum4881.graph DegreeTwoThreeSpectrum4134.graph
    sourceMap4281 fusedMap4281 sourceMap4281_checked fusedMap4281_checked
    DegreeTwoThreeFiniteComparisons.comparison4281
#print axioms sourceMap4281_checked
#print axioms fusedMap4281_checked
#print axioms certified4281
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
