/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4316 : Family 9 := level9.get ⟨396,by decide⟩
def sourceMap4316 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4316 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4316_checked : acceptsGraphIso
    (source (graph core4316) (root 9) 2 2) DegreeTwoThreeSpectrum4772.graph sourceMap4316=true := by decide +kernel
theorem fusedMap4316_checked : acceptsGraphIso
    (fused (graph core4316) (root 9) 2 2) DegreeTwoThreeSpectrum4350.graph fusedMap4316=true := by decide +kernel
theorem certified4316 : Certified (graph core4316) (root 9) 2 2 :=
  of_native_maps core4316 DegreeTwoThreeSpectrum4772.graph DegreeTwoThreeSpectrum4350.graph
    sourceMap4316 fusedMap4316 sourceMap4316_checked fusedMap4316_checked
    DegreeTwoThreeFiniteComparisons.comparison4316
#print axioms sourceMap4316_checked
#print axioms fusedMap4316_checked
#print axioms certified4316
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
