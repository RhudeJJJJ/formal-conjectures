/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4612 : Family 10 := level10.get ⟨638,by decide⟩
def sourceMap4612 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4612 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4612_checked : acceptsGraphIso
    (source (graph core4612) (root 10) 2 2) DegreeTwoThreeSpectrum7297.graph sourceMap4612=true := by decide +kernel
theorem fusedMap4612_checked : acceptsGraphIso
    (fused (graph core4612) (root 10) 2 2) DegreeTwoThreeSpectrum5332.graph fusedMap4612=true := by decide +kernel
theorem certified4612 : Certified (graph core4612) (root 10) 2 2 :=
  of_native_maps core4612 DegreeTwoThreeSpectrum7297.graph DegreeTwoThreeSpectrum5332.graph
    sourceMap4612 fusedMap4612 sourceMap4612_checked fusedMap4612_checked
    DegreeTwoThreeFiniteComparisons.comparison4612
#print axioms sourceMap4612_checked
#print axioms fusedMap4612_checked
#print axioms certified4612
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
