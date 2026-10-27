/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4308 : Family 9 := level9.get ⟨377,by decide⟩
def sourceMap4308 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4308 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4308_checked : acceptsGraphIso
    (source (graph core4308) (root 9) 2 2) DegreeTwoThreeSpectrum4750.graph sourceMap4308=true := by decide +kernel
theorem fusedMap4308_checked : acceptsGraphIso
    (fused (graph core4308) (root 9) 2 2) DegreeTwoThreeSpectrum4313.graph fusedMap4308=true := by decide +kernel
theorem certified4308 : Certified (graph core4308) (root 9) 2 2 :=
  of_native_maps core4308 DegreeTwoThreeSpectrum4750.graph DegreeTwoThreeSpectrum4313.graph
    sourceMap4308 fusedMap4308 sourceMap4308_checked fusedMap4308_checked
    DegreeTwoThreeFiniteComparisons.comparison4308
#print axioms sourceMap4308_checked
#print axioms fusedMap4308_checked
#print axioms certified4308
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
