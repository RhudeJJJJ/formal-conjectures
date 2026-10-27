/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4270 : Family 9 := level9.get ⟨273,by decide⟩
def sourceMap4270 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,8,9,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4270 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4270_checked : acceptsGraphIso
    (source (graph core4270) (root 9) 2 2) DegreeTwoThreeSpectrum4878.graph sourceMap4270=true := by decide +kernel
theorem fusedMap4270_checked : acceptsGraphIso
    (fused (graph core4270) (root 9) 2 2) DegreeTwoThreeSpectrum4087.graph fusedMap4270=true := by decide +kernel
theorem certified4270 : Certified (graph core4270) (root 9) 2 2 :=
  of_native_maps core4270 DegreeTwoThreeSpectrum4878.graph DegreeTwoThreeSpectrum4087.graph
    sourceMap4270 fusedMap4270 sourceMap4270_checked fusedMap4270_checked
    DegreeTwoThreeFiniteComparisons.comparison4270
#print axioms sourceMap4270_checked
#print axioms fusedMap4270_checked
#print axioms certified4270
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
