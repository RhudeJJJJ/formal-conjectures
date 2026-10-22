/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4212 : Family 9 := level9.get ⟨91,by decide⟩
def sourceMap4212 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,6,0,1,2,3,4,5,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4212 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (fusedLabel 9 2 2 v)
theorem sourceMap4212_checked : acceptsGraphIso
    (source (graph core4212) (root 9) 2 2) DegreeTwoThreeSpectrum4533.graph sourceMap4212=true := by decide +kernel
theorem fusedMap4212_checked : acceptsGraphIso
    (fused (graph core4212) (root 9) 2 2) DegreeTwoThreeSpectrum4057.graph fusedMap4212=true := by decide +kernel
theorem certified4212 : Certified (graph core4212) (root 9) 2 2 :=
  of_native_maps core4212 DegreeTwoThreeSpectrum4533.graph DegreeTwoThreeSpectrum4057.graph
    sourceMap4212 fusedMap4212 sourceMap4212_checked fusedMap4212_checked
    DegreeTwoThreeFiniteComparisons.comparison4212
#print axioms sourceMap4212_checked
#print axioms fusedMap4212_checked
#print axioms certified4212
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
