/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4372 : Family 9 := level9.get ⟨527,by decide⟩
def sourceMap4372 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,12,13,14,15,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 2 2 v)
def fusedMap4372 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4372_checked : acceptsGraphIso
    (source (graph core4372) (root 9) 2 2) DegreeTwoThreeSpectrum4710.graph sourceMap4372=true := by decide +kernel
theorem fusedMap4372_checked : acceptsGraphIso
    (fused (graph core4372) (root 9) 2 2) DegreeTwoThreeSpectrum4629.graph fusedMap4372=true := by decide +kernel
theorem certified4372 : Certified (graph core4372) (root 9) 2 2 :=
  of_native_maps core4372 DegreeTwoThreeSpectrum4710.graph DegreeTwoThreeSpectrum4629.graph
    sourceMap4372 fusedMap4372 sourceMap4372_checked fusedMap4372_checked
    DegreeTwoThreeFiniteComparisons.comparison4372
#print axioms sourceMap4372_checked
#print axioms fusedMap4372_checked
#print axioms certified4372
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
