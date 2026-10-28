/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5042 : Family 10 := level10.get ⟨1741,by decide⟩
def sourceMap5042 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap5042 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5042_checked : acceptsGraphIso
    (source (graph core5042) (root 10) 2 2) DegreeTwoThreeSpectrum7643.graph sourceMap5042=true := by decide +kernel
theorem fusedMap5042_checked : acceptsGraphIso
    (fused (graph core5042) (root 10) 2 2) DegreeTwoThreeSpectrum6587.graph fusedMap5042=true := by decide +kernel
theorem certified5042 : Certified (graph core5042) (root 10) 2 2 :=
  of_native_maps core5042 DegreeTwoThreeSpectrum7643.graph DegreeTwoThreeSpectrum6587.graph
    sourceMap5042 fusedMap5042 sourceMap5042_checked fusedMap5042_checked
    DegreeTwoThreeFiniteComparisons.comparison5042
#print axioms sourceMap5042_checked
#print axioms fusedMap5042_checked
#print axioms certified5042
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
