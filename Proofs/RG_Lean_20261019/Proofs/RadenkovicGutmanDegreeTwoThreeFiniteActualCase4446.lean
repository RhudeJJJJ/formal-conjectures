/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4446 : Family 10 := level10.get ⟨84,by decide⟩
def sourceMap4446 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4446 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4446_checked : acceptsGraphIso
    (source (graph core4446) (root 10) 2 2) DegreeTwoThreeSpectrum6460.graph sourceMap4446=true := by decide +kernel
theorem fusedMap4446_checked : acceptsGraphIso
    (fused (graph core4446) (root 10) 2 2) DegreeTwoThreeSpectrum5001.graph fusedMap4446=true := by decide +kernel
theorem certified4446 : Certified (graph core4446) (root 10) 2 2 :=
  of_native_maps core4446 DegreeTwoThreeSpectrum6460.graph DegreeTwoThreeSpectrum5001.graph
    sourceMap4446 fusedMap4446 sourceMap4446_checked fusedMap4446_checked
    DegreeTwoThreeFiniteComparisons.comparison4446
#print axioms sourceMap4446_checked
#print axioms fusedMap4446_checked
#print axioms certified4446
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
