/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4226 : Family 9 := level9.get ⟨134,by decide⟩
def sourceMap4226 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,11,12,13,14,15,8,9,10,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4226 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,7,8,9,10,11,12] (fusedLabel 9 2 2 v)
theorem sourceMap4226_checked : acceptsGraphIso
    (source (graph core4226) (root 9) 2 2) DegreeTwoThreeSpectrum4540.graph sourceMap4226=true := by decide +kernel
theorem fusedMap4226_checked : acceptsGraphIso
    (fused (graph core4226) (root 9) 2 2) DegreeTwoThreeSpectrum4169.graph fusedMap4226=true := by decide +kernel
theorem certified4226 : Certified (graph core4226) (root 9) 2 2 :=
  of_native_maps core4226 DegreeTwoThreeSpectrum4540.graph DegreeTwoThreeSpectrum4169.graph
    sourceMap4226 fusedMap4226 sourceMap4226_checked fusedMap4226_checked
    DegreeTwoThreeFiniteComparisons.comparison4226
#print axioms sourceMap4226_checked
#print axioms fusedMap4226_checked
#print axioms certified4226
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
