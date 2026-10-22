/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4428 : Family 9 := level9.get ⟨690,by decide⟩
def sourceMap4428 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap4428 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4428_checked : acceptsGraphIso
    (source (graph core4428) (root 9) 2 2) DegreeTwoThreeSpectrum4955.graph sourceMap4428=true := by decide +kernel
theorem fusedMap4428_checked : acceptsGraphIso
    (fused (graph core4428) (root 9) 2 2) DegreeTwoThreeSpectrum4665.graph fusedMap4428=true := by decide +kernel
theorem certified4428 : Certified (graph core4428) (root 9) 2 2 :=
  of_native_maps core4428 DegreeTwoThreeSpectrum4955.graph DegreeTwoThreeSpectrum4665.graph
    sourceMap4428 fusedMap4428 sourceMap4428_checked fusedMap4428_checked
    DegreeTwoThreeFiniteComparisons.comparison4428
#print axioms sourceMap4428_checked
#print axioms fusedMap4428_checked
#print axioms certified4428
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
