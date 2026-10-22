/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5037 : Family 10 := level10.get ⟨1725,by decide⟩
def sourceMap5037 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5037 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5037_checked : acceptsGraphIso
    (source (graph core5037) (root 10) 2 2) DegreeTwoThreeSpectrum7638.graph sourceMap5037=true := by decide +kernel
theorem fusedMap5037_checked : acceptsGraphIso
    (fused (graph core5037) (root 10) 2 2) DegreeTwoThreeSpectrum6527.graph fusedMap5037=true := by decide +kernel
theorem certified5037 : Certified (graph core5037) (root 10) 2 2 :=
  of_native_maps core5037 DegreeTwoThreeSpectrum7638.graph DegreeTwoThreeSpectrum6527.graph
    sourceMap5037 fusedMap5037 sourceMap5037_checked fusedMap5037_checked
    DegreeTwoThreeFiniteComparisons.comparison5037
#print axioms sourceMap5037_checked
#print axioms fusedMap5037_checked
#print axioms certified5037
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
