/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5027 : Family 10 := level10.get ⟨1703,by decide⟩
def sourceMap5027 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap5027 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5027_checked : acceptsGraphIso
    (source (graph core5027) (root 10) 2 2) DegreeTwoThreeSpectrum7628.graph sourceMap5027=true := by decide +kernel
theorem fusedMap5027_checked : acceptsGraphIso
    (fused (graph core5027) (root 10) 2 2) DegreeTwoThreeSpectrum6470.graph fusedMap5027=true := by decide +kernel
theorem certified5027 : Certified (graph core5027) (root 10) 2 2 :=
  of_native_maps core5027 DegreeTwoThreeSpectrum7628.graph DegreeTwoThreeSpectrum6470.graph
    sourceMap5027 fusedMap5027 sourceMap5027_checked fusedMap5027_checked
    DegreeTwoThreeFiniteComparisons.comparison5027
#print axioms sourceMap5027_checked
#print axioms fusedMap5027_checked
#print axioms certified5027
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
