/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4412 : Family 9 := level9.get ⟨631,by decide⟩
def sourceMap4412 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4412 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4412_checked : acceptsGraphIso
    (source (graph core4412) (root 9) 2 2) DegreeTwoThreeSpectrum4939.graph sourceMap4412=true := by decide +kernel
theorem fusedMap4412_checked : acceptsGraphIso
    (fused (graph core4412) (root 9) 2 2) DegreeTwoThreeSpectrum4391.graph fusedMap4412=true := by decide +kernel
theorem certified4412 : Certified (graph core4412) (root 9) 2 2 :=
  of_native_maps core4412 DegreeTwoThreeSpectrum4939.graph DegreeTwoThreeSpectrum4391.graph
    sourceMap4412 fusedMap4412 sourceMap4412_checked fusedMap4412_checked
    DegreeTwoThreeFiniteComparisons.comparison4412
#print axioms sourceMap4412_checked
#print axioms fusedMap4412_checked
#print axioms certified4412
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
