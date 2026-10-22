/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4451 : Family 10 := level10.get ⟨109,by decide⟩
def sourceMap4451 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4451 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4451_checked : acceptsGraphIso
    (source (graph core4451) (root 10) 2 2) DegreeTwoThreeSpectrum6778.graph sourceMap4451=true := by decide +kernel
theorem fusedMap4451_checked : acceptsGraphIso
    (fused (graph core4451) (root 10) 2 2) DegreeTwoThreeSpectrum5032.graph fusedMap4451=true := by decide +kernel
theorem certified4451 : Certified (graph core4451) (root 10) 2 2 :=
  of_native_maps core4451 DegreeTwoThreeSpectrum6778.graph DegreeTwoThreeSpectrum5032.graph
    sourceMap4451 fusedMap4451 sourceMap4451_checked fusedMap4451_checked
    DegreeTwoThreeFiniteComparisons.comparison4451
#print axioms sourceMap4451_checked
#print axioms fusedMap4451_checked
#print axioms certified4451
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
