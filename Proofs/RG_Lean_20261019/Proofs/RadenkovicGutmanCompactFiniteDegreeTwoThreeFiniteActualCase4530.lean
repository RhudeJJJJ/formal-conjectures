/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4530 : Family 10 := level10.get ⟨388,by decide⟩
def sourceMap4530 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4530 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4530_checked : acceptsGraphIso
    (source (graph core4530) (root 10) 2 2) DegreeTwoThreeSpectrum6809.graph sourceMap4530=true := by decide +kernel
theorem fusedMap4530_checked : acceptsGraphIso
    (fused (graph core4530) (root 10) 2 2) DegreeTwoThreeSpectrum5724.graph fusedMap4530=true := by decide +kernel
theorem certified4530 : Certified (graph core4530) (root 10) 2 2 :=
  of_native_maps core4530 DegreeTwoThreeSpectrum6809.graph DegreeTwoThreeSpectrum5724.graph
    sourceMap4530 fusedMap4530 sourceMap4530_checked fusedMap4530_checked
    DegreeTwoThreeFiniteComparisons.comparison4530
#print axioms sourceMap4530_checked
#print axioms fusedMap4530_checked
#print axioms certified4530
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
