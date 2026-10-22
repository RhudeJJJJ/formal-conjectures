/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4208 : Family 9 := level9.get ⟨78,by decide⟩
def sourceMap4208 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4208 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4208_checked : acceptsGraphIso
    (source (graph core4208) (root 9) 2 2) DegreeTwoThreeSpectrum4479.graph sourceMap4208=true := by decide +kernel
theorem fusedMap4208_checked : acceptsGraphIso
    (fused (graph core4208) (root 9) 2 2) DegreeTwoThreeSpectrum4017.graph fusedMap4208=true := by decide +kernel
theorem certified4208 : Certified (graph core4208) (root 9) 2 2 :=
  of_native_maps core4208 DegreeTwoThreeSpectrum4479.graph DegreeTwoThreeSpectrum4017.graph
    sourceMap4208 fusedMap4208 sourceMap4208_checked fusedMap4208_checked
    DegreeTwoThreeFiniteComparisons.comparison4208
#print axioms sourceMap4208_checked
#print axioms fusedMap4208_checked
#print axioms certified4208
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
