/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4427 : Family 9 := level9.get ⟨678,by decide⟩
def sourceMap4427 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,10,11,12,13,14,15,4,5,6,7,8,9] (sourceLabel 9 2 2 v)
def fusedMap4427 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4427_checked : acceptsGraphIso
    (source (graph core4427) (root 9) 2 2) DegreeTwoThreeSpectrum4954.graph sourceMap4427=true := by decide +kernel
theorem fusedMap4427_checked : acceptsGraphIso
    (fused (graph core4427) (root 9) 2 2) DegreeTwoThreeSpectrum4562.graph fusedMap4427=true := by decide +kernel
theorem certified4427 : Certified (graph core4427) (root 9) 2 2 :=
  of_native_maps core4427 DegreeTwoThreeSpectrum4954.graph DegreeTwoThreeSpectrum4562.graph
    sourceMap4427 fusedMap4427 sourceMap4427_checked fusedMap4427_checked
    DegreeTwoThreeFiniteComparisons.comparison4427
#print axioms sourceMap4427_checked
#print axioms fusedMap4427_checked
#print axioms certified4427
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
