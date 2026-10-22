/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5032 : Family 10 := level10.get ⟨1713,by decide⟩
def sourceMap5032 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5032 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5032_checked : acceptsGraphIso
    (source (graph core5032) (root 10) 2 2) DegreeTwoThreeSpectrum7633.graph sourceMap5032=true := by decide +kernel
theorem fusedMap5032_checked : acceptsGraphIso
    (fused (graph core5032) (root 10) 2 2) DegreeTwoThreeSpectrum6492.graph fusedMap5032=true := by decide +kernel
theorem certified5032 : Certified (graph core5032) (root 10) 2 2 :=
  of_native_maps core5032 DegreeTwoThreeSpectrum7633.graph DegreeTwoThreeSpectrum6492.graph
    sourceMap5032 fusedMap5032 sourceMap5032_checked fusedMap5032_checked
    DegreeTwoThreeFiniteComparisons.comparison5032
#print axioms sourceMap5032_checked
#print axioms fusedMap5032_checked
#print axioms certified5032
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
