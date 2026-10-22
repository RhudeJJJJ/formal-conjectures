/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4483 : Family 10 := level10.get ⟨230,by decide⟩
def sourceMap4483 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4483 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4483_checked : acceptsGraphIso
    (source (graph core4483) (root 10) 2 2) DegreeTwoThreeSpectrum6313.graph sourceMap4483=true := by decide +kernel
theorem fusedMap4483_checked : acceptsGraphIso
    (fused (graph core4483) (root 10) 2 2) DegreeTwoThreeSpectrum5281.graph fusedMap4483=true := by decide +kernel
theorem certified4483 : Certified (graph core4483) (root 10) 2 2 :=
  of_native_maps core4483 DegreeTwoThreeSpectrum6313.graph DegreeTwoThreeSpectrum5281.graph
    sourceMap4483 fusedMap4483 sourceMap4483_checked fusedMap4483_checked
    DegreeTwoThreeFiniteComparisons.comparison4483
#print axioms sourceMap4483_checked
#print axioms fusedMap4483_checked
#print axioms certified4483
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
